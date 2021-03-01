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
      (t, m) <- elabVec r tel ss
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

invert :: Tm -> AM [((String, Tel), [Subgoal])]
invert hyp = fold <$> (gamma >>= traverse try )
 where
  try :: CxE -> AM [((String, Tel), [Subgoal])]
  try (ByRule True ((gop, (h, tel)) :<= prems)) = cope (maAM (gop, hyp))
    (\ _ -> return [])
    (\ m -> return [((h, stan m tel), stan m prems)])
  try _ = return []

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

under :: Tm -> Tm -> String -> AM ()
under (TE lhs) (TE rhs) h = () <$ go lhs rhs where
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