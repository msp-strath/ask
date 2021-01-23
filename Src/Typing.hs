------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Typing                                       ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    TupleSections
  , LambdaCase
  , PatternSynonyms
  , TypeSynonymInstances
  , FlexibleInstances #-}
  
module Ask.Src.Typing where

--import Data.List
import Control.Applicative
import Data.Foldable
import Control.Monad
import Control.Arrow ((***))

import Debug.Trace

import Ask.Src.Bwd
import Ask.Src.Thin
import Ask.Src.Hide
import Ask.Src.HalfZip
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Context

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

hnfSyn :: Syn -> AM Syn
hnfSyn e@(TP (x, Hide ty)) = do
  nomBKind x >>= \case
    Defn t -> return (t ::: ty)
    _ -> return e
hnfSyn (t ::: ty) = do
  t <- hnf t
  ty <- hnf ty
  return (t ::: ty)
hnfSyn (f :$ s) = hnfSyn f >>= \case
  (TB b ::: TC "->" [dom, ran]) -> return ((b // (s ::: dom)) ::: ran)
  f -> return (f :$ s)
  
equal :: Tm -> (Tm, Tm) -> AM ()
equal ty (x, y) = guard $ x == y -- not for long


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


------------------------------------------------------------------------------
--  Elaboration
------------------------------------------------------------------------------

impQElabTm :: Tm -> Appl -> AM TmR
impQElabTm ty a = do
  push ImplicitQuantifier
  t <- elabTm ty a
  pop $ \case
    ImplicitQuantifier -> True
    _ -> False
  return t

elabTm :: Tm -> Appl -> AM TmR
elabTm ty a@(_, t) = ((`Our` a)) <$> go t
  where
    go :: Appl' -> AM Tm
    go ((t, _, y) :$$ ras) = case t of
      Lid -> do
        (e, sy) <- elabSyn y ras
        subtype sy ty
        return $ TE e
      _   -> do
        tel <- constructor ty y
        fst <$> elabTel y tel ras

elabTel :: String -> Tel -> [Appl] -> AM (Tm, Matching)
elabTel con tel as = do
  (ss, sch, po) <- cope (specialise tel as)
    (\ _ -> gripe (WrongNumOfArgs con (ari tel) as))
    return
  m <- argChk [] sch
  demand (PROVE po)
  return (stan m $ TC con ss, m)
 where
  specialise :: Tel -> [Appl] -> AM ([Tm], [((String, Tm), Appl)], Tm)
  specialise (Ex s b) as = do
    x <- hole s
    (ts, sch, po) <- specialise (b // x) as
    return (TE x : ts, sch, po)
  specialise ((x, s) :*: tel) (a : as) = do
    (ts, sch, po) <- specialise tel as
    return (TM x [] : ts, topInsert ((x, s), a) sch, po)
  specialise (Pr po) [] = return ([], [], po)
  specialise _ _ = gripe FAIL
  ari :: Tel -> Int
  ari (Ex s (K b)) = ari b
  ari (Ex s (L b)) = ari b
  ari (s :*: tel)  = 1 + ari tel
  ari (Pr _)       = 0

argChk :: Matching -> [((String, Tm), Appl)] -> AM Matching
argChk m [] = return m
argChk m (((x, t), a) : bs) = do
  a@(Our s _) <- elabTm (stan m t) a
  argChk ((x, s) : m) bs

elabSyn :: String -> [Appl] -> AM (Syn, Tm)
elabSyn f as = do
  f@(TP (_, Hide t)) <- what's f
  elabSpine (f, t) as

elabSpine :: (Syn, Tm) -> [Appl] -> AM (Syn, Tm)
elabSpine fsy [] = return fsy
elabSpine (f, sy) (a : as) = do
  (dom, ran) <- makeFun sy
  Our s _ <- elabTm dom a
  elabSpine (f :$ s, ran) as


------------------------------------------------------------------------------
--  Subtyping
------------------------------------------------------------------------------

subtype :: Tm -> Tm -> AM ()
subtype got want = unify Type got want  -- not gonna last

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

unify :: Tm -> Tm -> Tm -> AM ()
unify ty a b = do  -- pay more attention to types
  a <- hnf a
  b <- hnf b
  True <- track (show a ++ " =? " ++ show b) (return True)
  case (a, b) of
    (TC f as, TC g bs) -> do
      guard $ f == g
      tel <- constructor ty f
      unifies tel as bs
    (TE (TP xp), t) -> make xp t
    (s, TE (TP yp)) -> make yp s
    _ -> gripe FAIL

unifies :: Tel -> [Tm] -> [Tm] -> AM ()
unifies tel as bs = prepare tel as bs >>= execute [] where
  prepare :: Tel -> [Tm] -> [Tm] -> AM [((String, Tm), (Tm, Tm))]
  prepare (Pr _) [] [] = return []
  prepare (Ex s mo) (a : as) (b : bs) = do
    unify s a b
    prepare (mo // (a ::: s)) as bs
  prepare (xs :*: tel) (a : as) (b : bs) = do
    sch <- prepare tel as bs
    return $ topInsert (xs, (a, b)) sch
  execute :: Matching -> [((String, Tm), (Tm, Tm))] -> AM ()
  execute m [] = return ()
  execute m (((x, s), (a, b)) : sch) = do
    unify (stan m s) a b
    execute ((x, a) : m) sch

make :: (Nom, Hide Tm) -> Tm -> AM ()
make (x, _) (TE (TP (y, _))) | x == y = return ()
make (x, Hide ty) t = do
  nomBKind x >>= \case
    User _ -> gripe FAIL
    Defn s -> unify ty s t
    Hole -> do
      ga <- gamma
      ga <- go ga []
      setGamma ga
 where
  go B0 ms = gripe FAIL -- shouldn't happen
  go (ga :< Bind p@(y, _) Hole) ms | x == y = do
    pDep y (ms, t) >>= \case
      True -> gripe FAIL
      False -> return (ga <>< ms :< Bind p (Defn t))
  go (ga :< Bind (y, _) _) ms | x == y = gripe FAIL
  go (ga :< z@(Bind (y, _) k)) ms = do
    pDep y (ms, t) >>= \case
      False -> (:< z) <$> go ga ms
      True -> case k of
        User _ -> gripe FAIL
        _ -> go ga (z : ms)
  go (ga :< z) ms = (:< z) <$> go ga ms


------------------------------------------------------------------------------
--  Occur Check
------------------------------------------------------------------------------

class PDep t where
  pDep :: Nom -> t -> AM Bool

instance PDep Tm where
  pDep x t = do
    hnf t >>= \case
      TC _ ts -> pDep x ts
      TB t -> pDep x t
      TE e -> pDep x e

instance PDep Syn where
  pDep x (TP (y, _)) = return $ x == y
  pDep x (t ::: ty) = (||) <$> pDep x t <*> pDep x ty
  pDep x (e :$ s) =  (||) <$> pDep x e <*> pDep x s

instance PDep t => PDep [t] where
  pDep x ts = do
    any id <$> traverse (pDep x) ts

instance (PDep s, PDep t) => PDep (s, t) where
  pDep x (s, t) = (||) <$> pDep x s <*> pDep x t

instance PDep t => PDep (Bind t) where
  pDep x (K t) = pDep x t
  pDep x (L t) = pDep x t

instance PDep CxE where
  pDep x (Hyp p) = pDep x p
  pDep x (Bind (_, Hide ty) k) = (||) <$> pDep x ty <*> pDep x k
  pDep _ _ = return False

instance PDep BKind where
  pDep x (Defn t) = pDep x t
  pDep _ _ = return False


------------------------------------------------------------------------------
--  Constructor lookup
------------------------------------------------------------------------------

constructor :: Tm -> Con -> AM Tel
constructor ty con = do
  (d, ss) <- hnf ty >>= \case
    TC d ss -> return (d, ss)
    _ -> gripe (NonCanonicalType ty con)
  (fold <$> (gamma >>= traverse (try d ss con))) >>= \case
    [] -> gripe (DoesNotMake con ty)
    _ : _ : _ -> gripe (OverOverload con)
    [tel] -> return tel
 where
  try :: Con -> [Tm] -> Con -> CxE -> AM [Tel]
  try d ss c ((d', ps) ::> (c', tel)) | d == d' && c == c' = do
    m <- concat <$> ((mayhem $ halfZip ps ss) >>= traverse maAM)
    return [stan m tel]
  try _ _ _ _ = return []
  