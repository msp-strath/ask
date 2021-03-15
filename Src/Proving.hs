------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Proving                                      ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    LambdaCase
#-}

module Ask.Src.Proving where

import Data.Foldable
import Data.Traversable

import Ask.Src.Thin
import Ask.Src.Hide
import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Context
import Ask.Src.Typing

import Debug.Trace

trice = const id

by :: Tm -> Appl -> AM TmR
by goal a@(_, (t, _, r) :$$ ss) | elem t [Uid, Sym] = do
  subses <- fold <$> (gamma >>= traverse backchain)
  case subses of
    [(tel, subs)] -> do
      (t, m) <- elabVec EXP r tel ss
      mapM_ fred (stan m subs)
      return $ Our t a
    []     -> gripe $ ByBadRule r goal
    _      -> gripe $ ByAmbiguous r goal
 where
  backchain :: CxE -> AM [(Tel, [Subgoal])] -- list of successes
  backchain (ByRule _ ((gop, (h, tel)) :<= prems))
    | h == r = 
    cope (do
      m <- maAM (gop, goal)
      return [(stan m tel, stan m prems)])
      (\ _ -> return [])
      return
  backchain _ = return []
by goal r = gripe $ NotARule r

invert :: Tm -> AM [([CxE], [Subgoal])]
invert hyp = fold <$> (gamma >>= traverse try )
 where
  try :: CxE -> AM [([CxE], [Subgoal])]
  try (ByRule True ((gop, (h, tel)) :<= prems)) = do
    doorStop
    m <- prayTel [] tel
    gingerly m Prop gop hyp >>= \case
      [(_, m)] -> do
        de <- doorStep
        return [(de, stan m prems)]
      _ -> doorStep *> return []
  try _ = return []

prayTel :: Matching -> Tel -> AM Matching
prayTel m (Pr hs) = do
  for (stan m hs) $ \ h -> push $ Hyp True h
  return m
prayTel m (Ex s b) = do
  xn <- fresh "x"
  let u = "x" ++ show (snd (last xn)) -- BOO!
  let xp = (xn, Hide (stan m s))
  push $ Bind xp (User u)
  prayTel m (b // TP xp)
prayTel m ((x, s) :*: t) = do
  xn <- fresh x
  let u = x ++ show (snd (last xn)) -- BOO!
  let xp = (xn, Hide (stan m s))
  push $ Bind xp (User u)
  prayTel ((x, TE (TP xp)) : m) t

prayPat :: Matching -> Tm -> Pat -> AM (Syn, Matching)
prayPat m ty (PC c ps) = do
  ty <- hnf $ stan m ty
  tel <- constructor PAT ty c
  (ts, m) <- prayPats m tel ps
  return (TC c ts ::: ty, m)
prayPat m ty (PM x _) = do
  xn <- fresh x
  let u = "x" ++ show (snd (last xn)) -- BOO!
  let xp = (xn, Hide (stan m ty))
  push $ Bind xp (User u)
  return (TP xp, (x, TE (TP xp)) : m)

prayPats :: Matching -> Tel -> [Pat] -> AM ([Tm], Matching)
prayPats m (Pr hs) [] = do
  for (stan m hs) $ \ h -> push $ Hyp True h
  return ([], m)
prayPats m (Ex s b) (p : ps) = do
  (e, m) <- prayPat m s p
  (ts, m) <- prayPats m (b // e) ps
  return (upTE e : ts, m)
prayPats m ((x, s) :*: tel) (p : ps) = do
  (e, m) <- prayPat m s p
  (ts, m) <- prayPats ((x, upTE e) : m) tel ps
  return (upTE e : ts, m)
prayPats _ _ _ = gripe Mardiness

gingerly :: Matching -> Tm -> Pat -> Tm -> AM [(Syn, Matching)]
gingerly m ty p@(PC gc ps) t = hnf t >>= \case
  TC hc ts | gc /= hc -> return [] | otherwise -> do
    let ty' = stan m ty
    tel <- constructor PAT ty' gc
    gingerlies [] tel ps ts >>= \case
      [(us, m)] -> return [(TC gc us ::: ty', m)]
      _ -> return []
  t -> do
    let ty' = case t of
          TE (TP (_, Hide ty)) -> ty -- would like a size if it's there
          _ -> ty
    (e, m) <- prayPat m ty' p
    push . Hyp True $ TC "=" [ty', t, upTE e]
    return [(e, m)]
gingerly m ty (PM x th) t = case thicken th t of
  Nothing -> return []
  Just u -> return [(t ::: stan m ty, (x, u) : m)]
gingerly _ _ _ _ = gripe Mardiness


gingerlies :: Matching -> Tel -> [Pat] -> [Tm] -> AM [([Tm], Matching)]
gingerlies m (Pr hs) [] [] = do
  for (stan m hs) $ \ h -> push $ Hyp True h
  return [([], m)]
gingerlies m (Ex s b) (p : ps) (t : ts) = gingerly m s p t >>= \case
  [(e, m)] -> gingerlies m (b // e) ps ts >>= \case
    [(us, m)] -> return [(upTE e : us, m)]
    _ -> return []
  _ -> return []
gingerlies m ((x, s) :*: tel) (p : ps) (t : ts) = gingerly m s p t >>= \case
  [(e, m)] -> let u = upTE e in
    gingerlies ((x, u) : m) tel ps ts >>= \case
      [(us, m)] -> return [(u : us, m)]
      _ -> return []
  _ -> return []
gingerlies _ _ _ _ = return []

given :: Tm -> AM Bool{-proven?-}
given goal = do
  ga <- gamma
  True <- trice ("GIVEN: " ++ show goal ++ " from?\n" ++
             show (filter (\case {Bind _ _ -> True; Hyp _ _ -> True; _ -> False})
             (ga <>> [])))
           $ return True
  go ga
 where
  go B0 = gripe $ NotGiven goal
  go (ga :< Hyp b hyp) = cope (do
    True <- trice ("TRYING " ++ show hyp) $ return True
    doorStop
    smegUp hyp
    cope (unify (TC "Prop" []) hyp goal)
      (\ gr -> trice "OOPS" $ gripe gr)
      return
    doorStep
    True <- trice "BINGO" $ return True    
    return b
    )
    (\ gr -> go ga) return
  go (ga :< _) = go ga


smegUp :: Tm -> AM ()
smegUp (TE e) = smegDown e
smegUp (TC _ hs) = () <$ traverse smegUp hs
smegUp (TB (L t)) = smegUp t
smegUp (TB (K t)) = smegUp t
smegUp _ = return ()

smegDown :: Syn -> AM ()
smegDown (TP xp@(x, Hide ty)) =
  cope (nomBKind x)
    (\ _ -> do
      ty <- hnf ty
      push $ Bind xp Hole
      True <- trice ("GUESS: " ++ show x ++ " " ++ show ty) $ return True
      return ())
    (\ _ -> return ())
smegDown (tm ::: ty) = smegUp tm >> smegUp ty
smegDown (f :$ s) = smegDown f >> smegUp s
smegDown (TF _ as bs) = traverse smegUp as >> traverse smegUp bs >> return ()
smegDown _ = return ()

(|-) :: Tm -> AM x -> AM x
h |- p = do
  h <- normAQTy h
  push (Hyp True h)
  x <- p
  pop $ \case
    Hyp _ _ -> True
    _ -> False
  return x

splitProof
  :: (Nom, Hide Tm) -- thing to split
  -> Tm -- its type
  -> Tm  -- goal
  -> (Con, Tel) -- a candidate constructor and its telescope
  -> AM () -- generate relevant demands
splitProof xp@(xn, _) ty goal (c, tel) = quan B0 tel >>= demand
 where
  quan :: Bwd Tm -> Tel -> AM Subgoal
  quan sz (Ex s b) =
    ("", s) |:- \ e@(TP (yn, _)) ->
      (EVERY s . (yn \\)) <$> quan (sz :< TE e) (b // e)
  quan sz ((y, s) :*: tel) =
    (y, s) |:- \ e@(TP (yn, _)) ->
      (EVERY s . (yn \\)) <$> quan (sz :< TE e) (stan [(y, TE e)] tel)
  quan sz (Pr hs) = let tm = TC c (sz <>> []) in
    return $ foldr GIVEN
      (GIVEN (TC "=" [ty, TE (TP xp), tm]) $
         PROVE ((xn \\ goal) // (tm ::: ty)))
      hs

under :: Tm -> Tm -> Appl -> AM ()
under (TE lhs) (TE rhs) (_, (_, _, h) :$$ []) = () <$ go lhs rhs where
  go (e :$ a) (f :$ b) = do
    ty <- go e f
    hnf ty >>= \case
      TC "->" [dom, ran] -> do
        fred . PROVE $ TC "=" [dom, a, b]
        return ran
      _ -> gripe FAIL
  go (TP (xn, Hide ty)) (TP (yn, _)) | xn == yn = nomBKind xn >>= \case
    User k | k == h -> return ty
    _ -> gripe FAIL
  go (TF (f, Hide sch) as bs) (TF (g, _) cs ds)
    | fst (last f) == h && fst (last g) == h
    = mo sch as bs cs ds
  go _ _ = gripe FAIL
  mo (Al s t) (a : as) bs (c : cs) ds = do
    equal s (a, c)
    mo (t // (a ::: s)) as bs cs ds
  mo (iss :>> t) [] bs [] ds = so [] iss bs ds where
    so m [] [] [] = return $ stan m t
    so m ((x, s) : ss) (b : bs) (d : ds) = do
      fred . PROVE $ TC "=" [stan m t, b, d]
      so ((x, b) : m) ss bs ds
    so _ _ _ _ = gripe FAIL
  mo _ _ _ _ _ = gripe FAIL
under _ _ f = gripe FAIL