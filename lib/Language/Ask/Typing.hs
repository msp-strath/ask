------------------------------------------------------------------------------
----------                                                          ----------
----------     Typing                                               ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    TupleSections
  , LambdaCase
  , PatternSynonyms
  , TypeSynonymInstances
  , FlexibleInstances #-}

module Language.Ask.Typing where

--import Data.List
import Control.Applicative
import Data.Foldable
import Control.Monad
import Control.Arrow ((***))
import Data.Traversable
import Data.List hiding ((\\))

import Debug.Trace

import Language.Ask.Bwd
import Language.Ask.Thin
import Language.Ask.Hide
import Language.Ask.HalfZip
import Language.Ask.Lexing
import Language.Ask.RawAsk
import Language.Ask.Tm
import Language.Ask.Glueing
import Language.Ask.Context

track = const id


------------------------------------------------------------------------------
--  Head normalisation
------------------------------------------------------------------------------

hnf :: Tm -> AM Tm
hnf t = case t of
  TC _ _ -> return t
  TB _ -> return t
  TE e -> upsilon <$> hnfSyn e

upsilon :: Syn -> Tm
upsilon (t ::: _) = t
upsilon e = TE e

fnarg :: Syn -> [Tm] -> Maybe (Nom, Sch, [Tm], [Tm], [Tm])
fnarg (e :$ s) ss = fnarg e (s : ss)
fnarg (TF (f, Hide sch) is as) ss = Just (f, sch, is, as, ss)
fnarg (TE e ::: _) ss = fnarg e ss
fnarg _        _  = Nothing

hnfSyn :: Syn -> AM Syn
hnfSyn e | track ("HNFSYN " ++ show e) False = undefined
hnfSyn e = case fnarg e [] of
  Nothing -> hnfSyn' e
  Just (f, sch, is, as, ss) -> do
    let red ((g, ps) :=: e) | f == g = [(ps, e)]
        red _ = []
        run :: [([Pat], Syn)] -> [Tm] -> AM Syn
        run [] ts = return $ foldl (:$) (TF (f, Hide sch) is' as') ss' where
          (is', us) = blump is ts
          (as', ss') = blump as us
        run ((ps, e) : prog) ts = snarf ps ts >>= \case
          Left ts -> run prog ts
          Right (m, ts) -> hnfSyn $ foldl (:$) (stan m e) ts
    prog <- foldMap red <$> gamma
    run prog (is ++ as ++ ss)
 where
  snarf :: [Pat] -> [Tm] -> AM (Either [Tm] (Matching, [Tm]))
  snarf [] ts = return $ Right ([], ts)
  snarf (p : ps) [] = return $ Left []
  snarf (p : ps) (t : ts) = maKAM (p, t) >>= \case
    (t, Nothing) -> return $ Left (t : ts)
    (t, Just m) -> snarf ps ts >>= \case
      Left ts -> return $ Left (t : ts)
      Right (m', ts) -> return $ Right (m ++ m', ts)
  blump [] xs = ([], xs)
  blump (_ : ys) [] = ([], [])
  blump (_ : ys) (x : xs) = ((x :) *** id) (blump ys xs)

hnfSyn' :: Syn -> AM Syn
hnfSyn' e@(TP (x, Hide ty)) = cope
  (nomBKind x >>= \case
    Defn t -> do
      t <- hnf t
      ty <- hnf ty
      return (t ::: ty)
    _ -> return e)
  (\ _ -> return e)
  return
hnfSyn' (t ::: ty) = do
  t <- hnf t
  ty <- hnf ty
  return (t ::: ty)
hnfSyn' (f :$ s) = hnfSyn f >>= \case
  (TB b ::: TC "->" [dom, ran]) -> return ((b // (s ::: dom)) ::: ran)
  (TE e ::: _) -> return (e :$ s)
  f -> return (f :$ s)
hnfSyn' e | track ("HNFSYN " ++ show e) True = return e

(|:-) :: (String, Tm) -> (Syn -> AM x) -> AM x
(x, s) |:- p = do
  xn <- fresh x
  let xp = (xn, Hide s)
  push $ Bind xp (User x)
  y <- p (TP xp)
  pop $ \case
    Bind (yn, _) _ | xn == yn -> True
    _ -> False
  return y

norm :: Tm -> AM Tm     -- this is a fake
norm t = hnf t >>= \case
  TC c ts -> TC c <$> traverse norm ts
  t -> return t

testRun :: Tm -> AM Tm
testRun t = hnf t >>= \case
  TC c ts -> TC c <$> traverse testRun ts
  TE s -> TE <$> testSyn s
  t -> return t
 where
  testSyn :: Syn -> AM Syn
  testSyn (e :$ s) = (:$) <$> testSyn e <*> testRun s
  testSyn t = return t
  

unsize :: Tm -> AM Tm
unsize ty = hnf ty >>= \case
  Sized ty _ _ -> return ty
  ty -> return ty

equal :: Tm -> (Tm, Tm) -> AM ()
equal ty (x, y) = do
  ty <- unsize ty
  x <- hnf x
  y <- hnf y
  case (x, y) of
    (TC "$" [a, TE (TP (z, _)), i], TC "$" [b, TE (TP (y, _)), j])
      | y == z && i == j -> equal Type (a, b)
    (TC c ss, TC d ts) | c == d -> do
      tel <- constructor EXP ty c
      equals tel ss ts
    (TB a, TB b) -> case ty of
      TC "->" [dom, ran] -> do
        ("", dom) |:- \ x -> equal ran (a // x, b // x)
      _ -> gripe NotEqual
    (TE e, TE f) -> eqSyn e f >> return ()
    _ -> gripe NotEqual

equals :: Tel -> [Tm] -> [Tm] -> AM ()
equals tel ss ts = go [] tel ss ts where
  go :: [((String, Tm), (Tm, Tm))] -> Tel -> [Tm] -> [Tm] -> AM ()
  go acc (Pr _) [] [] = hit [] acc
  go acc (Ex a b) (s : ss) (t : ts) = do
    equal a (s, t)
    go acc (b // (s ::: a)) ss ts
  go acc ((x, a) :*: b) (s : ss) (t : ts) =
    go (topInsert ((x, a), (s, t)) acc) b ss ts
  go _ _ _ _ = gripe NotEqual
  hit :: Matching -> [((String, Tm), (Tm, Tm))] -> AM ()
  hit m [] = return ()
  hit m (((x, a), (s, t)) : sch) = do
    equal (stan m a) (s, t)
    hit ((x, s) : m) sch

eqSyn :: Syn -> Syn -> AM Tm
eqSyn (TP (xn, Hide ty)) (TP (yn, _)) | xn == yn = hnf ty
eqSyn (t ::: ty) e = equal ty (t, upTE e) >> return ty
eqSyn e (t ::: ty) = equal ty (upTE e, t) >> return ty
eqSyn (f :$ s) (g :$ t) = do
  TC "->" [dom, ran] <- eqSyn f g
  equal dom (s, t)
  return ran
eqSyn (TF (f, Hide sch) as bs) (TF (g, _) cs ds) | f == g =
  eqFun sch (as, bs) (cs, ds)
eqSyn _ _ = gripe NotEqual

eqFun :: Sch -> ([Tm], [Tm]) -> ([Tm], [Tm]) -> AM Tm
eqFun (Al s t) (a : as, bs) (c : cs, ds) = do
  equal s (a, c)
  eqFun (t // (a ::: s)) (as, bs) (cs, ds)
eqFun (iss :>> t) ([], bs) ([], ds) = go [] iss t bs ds where
  go m [] t [] [] = return $ stan m t
  go m ((x, ty) : iss) t (b : bs) (d : ds) = do
    let ty' = stan m ty
    equal ty' (b, d)
    go ((x, b) : m) iss t bs ds
  go _ _ _ _ _ = gripe FAIL
eqFun _ _ _ = gripe FAIL


normAQTy :: Tm -> AM Tm
normAQTy (TC "=" [ty, l, r]) = do
  ty <- norm ty
  l <- normAQTy l
  r <- normAQTy r
  return $ TC "=" [ty, l, r]
normAQTy (TC c ss) = TC c <$> traverse normAQTy ss
normAQTy t = return t


------------------------------------------------------------------------------
--  Pattern Matching
------------------------------------------------------------------------------

maAM :: (Pat, Tm) -> AM Matching
maAM (p, t) = go mempty (p, t) where
  go :: Thinning -> (Pat, Tm) -> AM Matching
  go ph (PM m th, t) = ((:[]) . (m,)) <$> mayhem (thicken th (t <^> ph))
  go ph (PC x ps, t) = do
    TC y ts <- hnf t
    guard $ x == y
    pts <- mayhem $ halfZip ps ts
    concat <$> traverse (go ph) pts
  go ph (PB p, t) = hnf t >>= \ t -> case t of
    TB (K t) -> go (o' ph) (p, t)
    TB (L t) -> go (os ph) (p, t)
    _ -> gripe FAIL

maKAM :: (Pat, Tm) -> AM (Tm, Maybe Matching)
maKAM (p, t) = go mempty (p, t) where
  go :: Thinning -> (Pat, Tm) -> AM (Tm, Maybe Matching)
  go ph (PM m th, t) = (t,) <$> case thicken th (t <^> ph) of
    Nothing -> return Nothing
    Just t -> return (Just [(m, t)])
  go ph (PC x ps, t) = hnf t >>= \case
    t@(TC y ts) | x == y -> case halfZip ps ts of
      Nothing -> return (t, Nothing)
      Just pts -> traverse (go ph) pts >>= \ tmms ->
        return (TC y (map fst tmms), concat <$> traverse snd tmms)
    t -> return (t, Nothing)
  go ph (PB p, t) = hnf t >>= \ t -> case t of
    TB (K t) -> go (o' ph) (p, t) >>= \case
      (t, mm) -> return (TB (K t), mm)
    TB (L t) -> go (os ph) (p, t) >>= \case
      (t, mm) -> return (TB (L t), mm)
    t -> return (t, Nothing)


------------------------------------------------------------------------------
--  Elaboration
------------------------------------------------------------------------------

impQElabTm :: Tm -> Appl -> AM TmR
impQElabTm ty a = do
  push ImplicitQuantifier
  t <- elabTmR ty a
  pop $ \case
    ImplicitQuantifier -> True
    _ -> False
  return t

elabTmR :: Tm -> Appl -> AM TmR
elabTmR ty a = ((`Our` a)) <$> (elabTm EXP ty a >>= normAQTy)

synthy :: Context -> LexL -> Bool
synthy ga (Lid, _, _) = True
synthy ga (Sym, _, "::") = True
synthy ga (_, _, f) = any declared ga where
  declared (Declare g _ _) = f == g
  declared _ = False

checky :: LexL -> Bool
checky (Uid, _, _) = True
checky (Sym, _, "::") = False
checky (Sym, _, ':':_) = True
checky _ = False

-- here is some serious chewing gum and string
elabEq :: Appl -> Appl -> AM Tm
{- special case for equations which look like they were
   generated by case splitting, where we want to keep size info
   in order to confirm the smallness of things
-}
elabEq lhs@(_, (Lid, _, x) :$$ []) rhs@(_, c :$$ ras)
  | checky c && all kid ras  -- should really check these are out of scope
  = do
  (e, sy) <- elabSyn EXP x []
  sy <- hnf sy
  rhs <- elabTm PAT sy rhs
  sy <- norm sy
  return $ TC "=" [sy, TE e, rhs]
 where
  kid (_, (Lid, _ , y) :$$ []) = x /= y
  kid _ = False
elabEq lhs rhs = do
  ga <- gamma
  case lhs of
    (_, l@(_, _, f) :$$ as) | synthy ga l -> do
      (e, sy) <- elabSyn EXP f as
      sy <- unsize sy
      rhs <- elabTm EXP sy rhs
      sy <- norm sy
      return $ TC "=" [sy, TE e, rhs]
    _ -> case rhs of
      (_, l@(_, _, f) :$$ as) | synthy ga l -> do
        (e, sy) <- elabSyn EXP f as
        sy <- unsize sy
        lhs <- elabTm EXP sy lhs
        sy <- norm sy
        return $ TC "=" [sy, lhs, TE e]
      _ -> do
        ty <- TE <$> hole Type
        lhs <- cope (elabTm EXP ty lhs)
          (\ _ -> elabTm EXP ty rhs >> elabTm EXP ty lhs
          )
          return
        rhs <- elabTm EXP ty rhs
        ty <- norm ty
        return $ TC "=" [ty, lhs, rhs]

elabTm :: ConMode -> Tm -> Appl -> AM Tm
elabTm m ty (_, a) | track (show ty ++ " on " ++ show a) False = undefined
elabTm m ty (ls, (Sym, _, "=") :$$ [lhs, rhs]) = do
  unify Type ty Prop
  elabEq lhs rhs
elabTm m ty (ls, l@(_, _, y) :$$ ras) = do
  ga <- gamma
  case l of
    _ | synthy ga l -> do
      (e, sy) <- elabSyn m y ras
      cope (subtype sy ty) (\ _ -> do
        True <- track ("SOOTY-SEZ-NO " ++ show sy ++ " " ++ show ty) $ return True
        sy <- norm sy
        ty <- norm ty
        gripe $ Terror ls sy ty
        ) return
      return $ TE e
    (Und, _, _) -> do
      guard $ null ras
      x <- hole ty
      return (TE x)
    (t, _, y) | elem t [Uid, Sym] -> do
      tel <- constructor m ty y
      fst <$> elabVec m y tel ras
    _ -> gripe FAIL
 where


shitSort :: [((String, Tm), Appl)] -> AM [((String, Tm), Appl)]
shitSort [] = return []
shitSort (a@((_, _), (_, (Lid, _, f) :$$ _)) : as) = cope (what's f)
  (\ _ -> topInsert a <$> shitSort as)
  $ \case
    Right (_, ty) -> hnf ty >>= \case
      TC "$" _ -> topInsert a <$> shitSort as
      _ -> (a :) <$> shitSort as
    _ -> (a :) <$> shitSort as
shitSort (a@((_, _), (_, (_, _, "::") :$$ _)) : as) = (a :) <$> shitSort as
shitSort (a : as) = topInsert a <$> shitSort as

elabVec :: ConMode -> String -> Tel -> [Appl] -> AM (Tm, Matching)
elabVec cm con tel as = do
  (ss, sch, pos) <- cope (specialise tel as)
    (\ _ -> gripe (WrongNumOfArgs con (ari tel) as))
    return
  sch <- shitSort sch
  m <- argChk cm [] sch
  traverse (fred . PROVE) pos
  return (stan m $ TC con ss, m)
 where
  specialise :: Tel -> [Appl] -> AM ([Tm], [((String, Tm), Appl)], [Tm])
  specialise (Ex s b) as = do
    x <- hole s
    (ts, sch, po) <- specialise (b // x) as
    return (TE x : ts, sch, po)
  specialise ((x, s) :*: tel) (a : as) = do
    (ts, sch, po) <- specialise tel as
    return (TM x [] : ts, topInsert ((x, s), a) sch, po)
  specialise (Pr pos) [] = return ([], [], pos)
  specialise _ _ = gripe FAIL
  ari :: Tel -> Int
  ari (Ex s (K b)) = ari b
  ari (Ex s (L b)) = ari b
  ari (s :*: tel)  = 1 + ari tel
  ari (Pr _)       = 0

argChk :: ConMode -> Matching -> [((String, Tm), Appl)] -> AM Matching
argChk cd m [] = return m
argChk cd m (((x, t), a) : bs) = do
  s <- elabTm cd (stan m t) a
  argChk cd ((x, s) : m) bs

elabSyn :: ConMode -> String -> [Appl] -> AM (Syn, Tm)
elabSyn cm "::" (tm : ty : as) = do
  ty <- elabTm EXP Type ty
  tm <- elabTm cm ty tm
  elabSpine cm (tm ::: ty, ty) as
elabSyn cm f as = what's f >>= \case
  Right ety -> elabSpine cm ety as
  Left (n, sch) -> elabFun cm (n, Hide sch) B0 sch as

elabSpine :: ConMode -> (Syn, Tm) -> [Appl] -> AM (Syn, Tm)
elabSpine cm fsy [] = track (show fsy) $ return fsy
elabSpine cm (f, sy) (a : as) = do
  (dom, ran) <- makeFun sy
  s <- elabTm cm dom a
  elabSpine cm (f :$ s, ran) as

elabFun :: ConMode -> (Nom, Hide Sch) -> Bwd Tm -> Sch -> [Appl] -> AM (Syn, Tm)
elabFun cm (f, _) B0 sch as
  | track ("FUN (" ++ show f ++ " :: " ++ show sch ++ ")" ++ show as) False
  = undefined
elabFun cm f az (Al a s) as = do
  x <- hole a
  elabFun cm f (az :< TE x) (s // x) as
elabFun cm f az (iss :>> t) as = do
  (schd, bs) <- snarf iss as
  m <- argChk cm [] schd
  elabSpine cm (TF f (az <>> []) [t | (i, _) <- iss, (j, t) <- m, i == j], stan m t) bs
 where
  snarf :: [(String, Tm)] -> [Appl] -> AM ([((String, Tm), Appl)], [Appl])
  snarf [] as = return ([], as)
  snarf _  [] = gripe FAIL
  snarf (xty : xtys) (a : as) = do
    (schd, bs) <- snarf xtys as
    return (topInsert (xty, a) schd, bs)


------------------------------------------------------------------------------
--  Subtyping
------------------------------------------------------------------------------

-- I'm very far from convinced that I'm doing this right.

subtype :: Tm -> Tm -> AM ()
subtype s t = do
  s <- hnf s
  t <- hnf t
  go s t
 where
  go s t | track ("SOOTY " ++ show s ++ " " ++ show t) False = undefined
  go (TC "->" [s0, t0]) u =
    if subTm u [s0, t0]
    then gripe InfiniteType
    else do
      (s1, t1) <- makeFun u
      subtype s1 s0
      subtype t0 t1
  go u (TC "->" [s1, t1]) =
    if subTm u [s1, t1]
    then gripe InfiniteType
    else do
      (s0, t0) <- makeFun u
      subtype s1 s0
      subtype t0 t1
  go (TC "$" [ty0, non0, num0]) (TC "$" [ty1, non1, num1]) = do
    unify Type ty0 ty1
    unify Zone non0 non1
    greq num0 num1
  go (TC "$" [ty0, _, _]) ty1@(TC _ _) = unify Type ty0 ty1
  go got want = unify Type got want  -- not gonna last

greq :: Tm -> Tm -> AM ()
greq _ (TC "Z" []) = return ()
greq (TC "S" [m]) (TC "S" [n]) = greq m n
greq _ _ = gripe FAIL

makeFun :: Tm -> AM (Tm, Tm)
makeFun (TC "->" [dom, ran]) = return (dom, ran)
makeFun ty = do
  dom <- TE <$> hole Type
  ran <- TE <$> hole Type
  unify Type (dom :-> ran) ty
  return (dom, ran)


------------------------------------------------------------------------------
--  Unification
------------------------------------------------------------------------------

unify = unify' True
unify' :: Bool -> Tm -> Tm -> Tm -> AM ()
unify' heh ty a b = do  -- pay more attention to types
  ty <- unsize ty
  a <- if heh then hnf a else pure a
  b <- if heh then hnf b else pure b
  True <- track (show a ++ " =? " ++ show b) (return True)
  case (a, b) of
    (TC "$" [a, TE (TP (z, _)), i], TC "$" [b, TE (TP (y, _)), j])
      | z == y && i == j -> unify' heh Type a b
    (TC f as, TC g bs) -> do
      guardErr (f == g) (Unification f g)
      tel <- constructor EXP ty f
      unifies' heh tel as bs
    (TE (TP xp), t) -> make xp t ty
    (s, TE (TP yp)) -> make yp s ty
    (TE e, TE f) -> () <$ unifySyn' heh e f
    _ -> cope (equal ty (a, b))
      (\ _ -> do
        True <- track (show a ++ " /= " ++ show b) $ return True
        gripe FAIL)
      return

unfiySyn = unifySyn' True
unifySyn' :: Bool -> Syn -> Syn -> AM Tm   --- eeeevil
unifySyn' heh (TP xp@(_, Hide ty)) e = do
  ty <- eqSyn e e
  ty <$ make xp (TE e) ty
unifySyn' heh e (TP xp@(_, Hide ty)) = do
  ty <- eqSyn e e
  ty <$ make xp (TE e) ty
unifySyn' heh (e :$ a) (f :$ b) = do
  ty <- unifySyn' heh e f >>= hnf
  (dom, ran) <- makeFun ty
  ran <$ unify' heh dom a b
unifySyn' heh (TF (f, Hide sch) as bs) (TF (g, Hide _) cs ds) | f == g =
  unifyFun' heh sch (as , bs) (cs, ds)
unifySyn' heh (a ::: s) (b ::: t) = do
  unify' heh Type s t
  unify' heh s a b
  return s
unifySyn' _ _ _ = gripe FAIL

unifyFun = unifyFun' True
unifyFun' :: Bool -> Sch -> ([Tm], [Tm]) -> ([Tm], [Tm]) -> AM Tm
unifyFun' heh (Al s t) (a : as, bs) (c : cs, ds) = do
  unify' heh s a c
  unifyFun' heh (t // (a ::: s)) (as, bs) (cs, ds)
unifyFun' heh (iss :>> t) ([], bs) ([], ds) = go [] iss t bs ds where
  go m [] t [] [] = return $ stan m t
  go m ((x, ty) : iss) t (b : bs) (d : ds) = do
    let ty' = stan m ty
    unify' heh ty' b d
    go ((x, b) : m) iss t bs ds
  go _ _ _ _ _ = gripe FAIL
unifyFun' _ _ _ _ = gripe FAIL

prepareSubQs = prepareSubQs' True
prepareSubQs' :: Bool -> Tel -> [Tm] -> [Tm] -> AM [((String, Tm), (Tm, Tm))]
prepareSubQs' heh (Pr _) [] [] = return []
prepareSubQs' heh (Ex s mo) (a : as) (b : bs) = do
  unify' heh s a b
  prepareSubQs' heh (mo // (a ::: s)) as bs
prepareSubQs' heh (xs :*: tel) (a : as) (b : bs) = do
  sch <- prepareSubQs' heh tel as bs
  return $ topInsert (xs, (a, b)) sch

unifies = unifies' True
unifies' :: Bool -> Tel -> [Tm] -> [Tm] -> AM ()
unifies' heh tel as bs = prepareSubQs' heh tel as bs >>= execute [] where
  execute :: Matching -> [((String, Tm), (Tm, Tm))] -> AM ()
  execute m [] = return ()
  execute m (((x, s), (a, b)) : sch) = do
    unify' heh (stan m s) a b
    execute ((x, a) : m) sch

make :: (Nom, Hide Tm) -> Tm -> Tm -> AM ()
make (x, _) (TE (TP (y, _))) got | x == y = return ()
make (x, _) t got | track ("MAKE " ++ show x ++ " = " ++ show t) False = undefined
make xp@(x, Hide ty) t got = do
  de <- doorStep
  doorStop
  traverse push de
  True <- track ("seeking " ++ show x ++ "\n" ++ show de) $ return True
  k <- nomBKind x
  True <- track (show x ++ " is a " ++ show k) $ return True
  case k of
    User _ -> case t of
      TE (TP yp@(y, _)) -> nomBKind y >>= \case
        Hole -> make yp (TE (TP xp)) ty
        _ -> gripe FAIL
      _ -> gripe FAIL
    Defn s -> do
      True <- track ("BUT " ++ show x ++ " = " ++ show s) $ return True
      unify ty s t
    Hole -> do
      hnf ty >>= \case
        Sized _ _ _ -> do
          True <- track ("MAKE-SIZED " ++ show x ++ " " ++ show t) $ return True
          hnf t >>= \case
            TC c _ -> gripe $ InductiveHypsDon'tLike c
            TE _ -> return ()
            _ -> gripe Mardiness
        _ -> return ()
      got <- case t of
        TE e -> eqSyn e e
        _ -> return got
      subtype got ty
      ga <- gamma
      ga <- go ga []
      setGamma ga
      de <- doorStep
      doorStop
      traverse push de
      True <- track ("MADE\n" ++ show de) $ return True
      return ()
 where
  go B0 ms = do
    True <- track ("AWOL " ++ show x) $ return True
    gripe FAIL -- shouldn't happen
  go (ga :< z) ms | track ("MAKE-GO: " ++ show z ++ " " ++ show ms) False = undefined
  go (ga :< Bind p@(y, _) Hole) ms | x == y = case pDep y (ms, t) of
      True -> gripe FAIL
      False -> return (ga <>< ms :< Bind p (Defn t))
  go (ga :< Bind (y, _) _) ms | x == y = gripe FAIL
  go (ga :< z@(Bind (y, _) k)) ms = case pDep y (ms, t) of
      False -> (:< z) <$> go ga ms
      True -> case k of
        User _ -> gripe FAIL
        _ -> go ga (z : ms)
  go (ga :< z) ms = (:< z) <$> go ga ms


------------------------------------------------------------------------------
--  Occur Check
------------------------------------------------------------------------------

class PDep t where
  pDep :: Nom -> t -> Bool

instance PDep Tm where
  pDep x t = case t of
      TC _ ts -> pDep x ts
      TB t -> pDep x t
      TE e -> pDep x e

instance PDep Syn where
  pDep x (TP (y, _)) =  x == y
  pDep x (t ::: ty) = pDep x t || pDep x ty
  pDep x (e :$ s) =  pDep x e || pDep x s
  pDep x (TF _ is as) = pDep x is || pDep x as
  pDep x _ = False

instance PDep t => PDep [t] where
  pDep x ts = any id (map (pDep x) ts)

instance (PDep s, PDep t) => PDep (s, t) where
  pDep x (s, t) = pDep x s || pDep x t

instance PDep t => PDep (Bind t) where
  pDep x (K t) = pDep x t
  pDep x (L t) = pDep x t

instance PDep CxE where
  pDep x (Hyp _ p) = pDep x p
  pDep x (Bind (_, Hide ty) k) = pDep x ty || pDep x k
  pDep _ _ = False

instance PDep BKind where
  pDep x (Defn t) = pDep x t
  pDep _ _ = False


------------------------------------------------------------------------------
--  Obtaining a Telescope from a Template
------------------------------------------------------------------------------

elabTel :: [Appl] -> AM Tel
elabTel as = do
  doorStop
  phs <- placeHolders as
  lox <- doorStep
  telify (map fst phs) lox

placeHolders :: [Appl] -> AM [(String, Tm)]
placeHolders as = do
  let decolonise i (_, (Sym, _, "::") :$$ [(_, (Lid, _, x) :$$ []) , ty]) =
        (x, ty)
      decolonise i ty = ("#" ++ show i, ty)
  let phs  = zipWith decolonise [0..] as
  guard $ nodup (map fst phs)
  sch <- mayhem $ map fst <$> topSort (map (, ()) phs)
  xts <- for sch $ \ (x, a) -> do
    ty <- elabTm EXP Type a
    xn <- fresh x
    push (Bind (xn, Hide ty) (User x))
    return (x, ty)
  for phs $ \ (x, _) -> (x,) <$> mayhem (lookup x xts)

telify :: [String]  -- the explicit parameter order
       -> [CxE]     -- the local context (as returned by doorStep)
       -> AM Tel    -- the telescope
telify vs lox = go [] lox where
  go ps [] = do
    xs <- traverse (\ x -> mayhem $ (x,) <$> (snd <$> lookup x ps)) vs
    return $ foldr (:*:) (Pr []) xs
  go ps (Bind (xp, Hide ty) bk : lox) = case bk of
    Defn t -> e4p (xp, t ::: ty) <$> go ps lox
    Hole -> do
      bs <- traverse (\ (_, (xp, _)) -> return $ pDep xp ty) ps
      guard $ all not bs
      Ex ty <$> ((xp \\) <$> go ps lox)
    User x -> e4p (xp, TM x [] ::: ty) <$> go ((x, (xp, ty)) : ps) lox
  go ps ((_ ::> _) : lox) = go ps lox
  go _ _ = gripe FAIL

schemify :: [String]  -- the explicit parameter order
         -> [CxE]     -- the local context (as returned by doorStep)
         -> Tm        -- the return type
         -> AM Sch    -- the type scheme
schemify vs lox rt = go [] lox where
  go ps [] = do
    xs <- traverse (\ x -> mayhem $ (x,) <$> (snd <$> lookup x ps)) vs
    return $ xs :>> rt
  go ps (Bind (xp, Hide ty) bk : lox) = case bk of
    Defn t -> e4p (xp, t ::: ty) <$> go ps lox
    Hole -> do
      bs <- traverse (\ (_, (xp, _)) -> return $ pDep xp ty) ps
      guard $ all not bs
      Al ty <$> ((xp \\) <$> go ps lox)
    User x
      | x `elem` vs ->
        e4p (xp, TM x [] ::: ty) <$> go ((x, (xp, ty)) : ps) lox
      | otherwise -> do
        bs <- traverse (\ (_, (xp, _)) -> return $ pDep xp ty) ps
        guard $ all not bs
        Al ty <$> ((xp \\) <$> go ps lox)
  go ps ((_ ::> _) : lox) = go ps lox
  go _ _ = gripe FAIL


------------------------------------------------------------------------------
--  Binding a Parameter List
------------------------------------------------------------------------------

bindParam :: [Appl] -> AM ([String], [(Nom, Syn)])
bindParam as = do
  push ImplicitQuantifier
  (xs, sb) <- fold <$> traverse go as
  pop (\case {ImplicitQuantifier -> True; _ -> False})
  guard $ nodup xs
  return (xs, sb)
 where
  go :: Appl -> AM ([String], [(Nom, Syn)])
  go (_, a) = do
    (x, ty) <- case a of
      (Sym, _, "::") :$$ [(_, (Lid, _, x) :$$ []), ty] -> return (x, ty)
      (Lid, _, x) :$$ [] -> return (x, ([], (Und, (0,0), "_") :$$ []))
      _ -> gripe FAIL
    ty <- elabTm EXP Type ty
    xn <- fresh x
    push (Bind (xn, Hide ty) (User x))
    return ([x], [(xn, (TM x [] ::: ty))])


------------------------------------------------------------------------------
--  Duplication Freeness
------------------------------------------------------------------------------

nodup :: Eq x => [x] -> Bool
nodup [] = True
nodup (x : xs)
  | elem x xs = False
  | otherwise = nodup xs


------------------------------------------------------------------------------
--  Constructor lookup
------------------------------------------------------------------------------

-- it is not safe to allow *construction* in sized types
-- defined foo (n :: Nat) :: Nat induction n
--   given foo (n :: Nat) :: Nat define foo n from n
--     defined foo Z = Z
--     defined foo (S n) = foo (S Z) -- no reason to believe Z is small enough

data ConMode = PAT | EXP deriving (Show, Eq)

constructor :: ConMode -> Tm -> Con -> AM Tel
constructor m ty con = cope
  (conSplit m ty >>= \ cts -> mayhem $ lookup con cts)
  (\ _ ->  do
    (d, ss) <- hnf ty >>= \case
      TC d ss -> return (d, ss)
      ty -> (foldMap (conCand con) <$> gamma) >>= \case
        [(p, tel)] -> do
          (TC d ss, m) <- splat Type p
          subtype (TC d ss) ty
          return (d, ss)
        _ -> gripe $ NonCanonicalType ty con
    (fold <$> (gamma >>= traverse (try d ss con))) >>= \case
      [] -> gripe (DoesNotMake con ty)
      _ : _ : _ -> gripe (OverOverload con)
      [tel] -> return tel)
   return
 where
  try :: Con -> [Tm] -> Con -> CxE -> AM [Tel]
  try d ss c ((d', ps) ::> (c', tel)) | d == d' && c == c' = do
    m <- concat <$> ((mayhem $ halfZip ps ss) >>= traverse maAM)
    return [stan m tel]
  try d ss c (Data _ de) =
    concat <$> traverse (try d ss c) de
  try _ _ _ _ = return []
  {-
  cand :: CxE -> [(Pat, Tel)]
  cand ((c, ps) ::> (k, tel)) | k == con = [(PC c ps, tel)]
  cand (Data _ de) = foldMap cand de
  cand _ = []
  -}
  splat :: Tm -> Pat -> AM (Tm, Matching)
  splat ty (PM x _{- er? -}) = do
    y <- hole ty
    return (TE y, [(x, TE y)])
  splat ty (PC c ps) = do
    tel <- constructor PAT ty c
    (ts, m) <- splats [] tel ps
    return (TC c ts, m)
  splat _ _ = gripe FAIL
  splats m (Ex s tel) (p : ps) = do
    x <- hole s
    (ts, m) <- splats m (tel // x) ps
    return (TE x : ts, m)
  splats m ((x, s) :*: tel) (p : ps) = do
    -- this is broken in general
    (t, m) <- splat (stan m s) p
    (ts, m) <- splats m tel ps
    return (t : ts, m)
  splats m (Pr _) [] = return ([], m)
  splats _ _ _ = gripe FAIL

conCand :: Con -> CxE -> [(Pat, Tel)]
conCand con ((c, ps) ::> (k, tel)) | k == con = [(PC c ps, tel)]
conCand con (Data _ de) = foldMap (conCand con) de
conCand _ _ = []

-- FIXME: don't assume quite so casually that things are covariant functors
weeer :: Con  -- type constructor to be monkeyed
      -> Tm   -- the nonce
      -> Tm   -- the smaller size
      -> Tel  -- the telescope of raw constructor arguments
      -> Tel  -- the telescope of smaller constructor arguments
weeer d non num (Ex a tel) = Ex a (fmap (weeer d non num) tel)
weeer d non num ((x, s) :*: tel) = (x, hit s) :*: weeer d non num tel where
  hit ty@(TC c ts)
    | c == d = TC "$" [TC c (map hit ts), non, num]
    | otherwise = TC c (map hit ts)
  hit t = t
weeer d non num (Pr pos) = Pr pos

conSplit :: ConMode -> Tm -> AM [(Con, Tel)]
conSplit m t = do
  t <- hnf t
  z@(monkey, d, ts) <- case t of
    TC "$" [TC d ts, non, num] -> case m of
      PAT -> return (weeer d non (TC "S" [num]), d, ts)
      EXP -> gripe NoSizedConstruction
    TC d ts -> return (id, d, ts)
    _ -> gripe FAIL
  (foldMap (\case {Data e de | d == e -> [de]; _ -> []}) <$> gamma) >>= \case
    [de] -> concat <$> traverse (refine z) de
    _ -> gripe $ NotADataType t
 where
  refine :: (Tel -> Tel, Con, [Tm]) -> CxE -> AM [(Con, Tel)]
  refine (monkey, d, ts) ((e, ps) ::> (c, tel)) | d == e = cope (do
    m <- concat <$> ((mayhem $ halfZip ps ts) >>= traverse maAM)
    return [(c, stan m (monkey tel))]
    )
    (\ _ -> return [])
    return
  refine _ _ = return []


------------------------------------------------------------------------------
--  Fred
------------------------------------------------------------------------------

tested :: Tm -> Tm -> Tm -> AM ()
tested ty lhs rhs = flip (cope (equal ty (lhs, rhs))) return $ \ _ -> do
  ty  <- unsize ty
  lhs <- hnf lhs
  rhs <- hnf rhs
  case (ty, lhs, rhs) of
    (TC d _, TC a _, TC b _)
      | a /= b && d /= "Prop" -> demand . PROVE $ FALSE
    (_, TC c ss, TC d ts) | c == d -> do
      tel <- constructor EXP ty c
      testSubterms tel ss ts
    _ -> do
      ga <- gamma
      True <- track ("FRED: " ++ show ty ++ " " ++ show lhs ++ " " ++ show rhs ++ "\n" ++ show ga)
        $ return True
      demand . PROVE $ TC "=" [ty, lhs, rhs]

testSubterms :: Tel -> [Tm] -> [Tm] -> AM ()
testSubterms tel ss ts = go [] tel ss ts where -- cargo cult
  go :: [((String, Tm), (Tm, Tm))] -> Tel -> [Tm] -> [Tm] -> AM ()
  go acc (Pr _) [] [] = hit [] acc
  go acc (Ex a b) (s : ss) (t : ts) = do
    tested a s t
    go acc (b // (s ::: a)) ss ts
  go acc ((x, a) :*: b) (s : ss) (t : ts) =
    go (topInsert ((x, a), (s, t)) acc) b ss ts
  go _ _ _ _ = gripe NotEqual
  hit :: Matching -> [((String, Tm), (Tm, Tm))] -> AM ()
  hit m [] = return ()
  hit m (((x, a), (s, t)) : sch) = do
    tested (stan m a) s t
    hit ((x, s) : m) sch

fred :: Subgoal -> AM ()
fred (PROVE g) = hnf g >>= \case
  TC "=" [ty, lhs, rhs] -> tested ty lhs rhs
  _ -> demand $ PROVE g
fred s = demand s
