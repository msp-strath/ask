{-# LANGUAGE CPP, TupleSections, LambdaCase, PatternSynonyms,
    TypeSynonymInstances, FlexibleInstances #-}
module Ask.Src.Scoping where

import Data.List
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Applicative
import qualified Data.Map as M
import Data.Foldable
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

track = trace

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String  -- dear god no, fix this to be locally nameless
  | Bind (Nom, Hide Tm) BKind
  | ImplicitQuantifier
  | (Con, [Pat]) ::> (Con, [(String, Tm)])
  | ByRule Bool{- pukka intro?-} Rule
  deriving (Show, Eq) -- get rid of that Eq!

data Rule =
  (Pat, (Con, [(String, Tm)])) :<=
  [ Tm
  ]
  deriving (Show, Eq)

data BKind
  = User String
  | Defn Tm
  | Hole
  deriving (Show, Eq)

data Gripe
  = Surplus
  | Scope String
  | ByBadRule
  | FromNeedsConnective
  | NotGiven
  | NotEqual
  | NotARule
  | ByAmbiguous
  | Mardiness
  | BadSubgoal
  | WrongNumOfArgs Con
  | DoesNotMake Con Con
  | OverOverload Con
  | FAIL
  deriving (Show, Eq)

type Root = (Bwd (String, Int), Int)

data AM x = AM {runAM
  :: Setup     -- rules and stuff
  -> AskState  -- vars and hyps
  -> Either Gripe (x, AskState)}

data AskState = AskState
  { context :: Context
  , root    :: Root
  } deriving Show

instance Monad AM where
  return x    = AM $ \ _ as -> Right (x, as)
  AM f >>= k = AM $ \ setup as -> case f setup as of
    Left g -> Left g
    Right (x, as) -> runAM (k x) setup as
#if !(MIN_VERSION_base(4,13,0))
  -- Monad(fail) will be removed in GHC 8.8+
  fail = Fail.fail
#endif
instance Applicative AM where pure = return; (<*>) = ap
instance Functor AM where fmap = ap . return

instance Fail.MonadFail AM where
  fail _ = AM $ \ _ _ -> Left FAIL

gripe :: Gripe -> AM x
gripe g = AM $ \ _ _ -> Left g

mayhem :: Maybe x -> AM x
mayhem mx = do
  Just x <- return mx
  return x

cope :: AM x -> (Gripe -> AM y) -> (x -> AM y) -> AM y
cope (AM f) yuk wow = AM $ \ setup as -> case f setup as of
  Left g        -> runAM (yuk g) setup as
  Right (x, as) -> runAM (wow x) setup as

instance Alternative AM where
  empty = gripe FAIL
  ma <|> mb = cope ma (const mb) return

data Setup = Setup
  { fixities   :: FixityTable
  } deriving Show

fixity :: String -> AM (Int, Assocy)
fixity o = AM $ \ s as -> Right . (, as) $ case M.lookup o (fixities s) of
  Nothing -> (9, LAsso)
  Just x  -> x

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

by :: Tm -> Appl -> AM (TmR, [Tm])
by goal a@(_, (t, _, _) :$$ _) | elem t [Uid, Sym] = do
  subses <- fold <$> (gamma >>= traverse (backchain a))
  case subses of
    [subs] -> return subs
    []     -> gripe ByBadRule
    _      -> gripe ByAmbiguous
 where
  backchain :: Appl -> CxE -> AM [(TmR, [Tm])] -- list of successes
  backchain a@(_, (_, _, r) :$$ ss) (ByRule _ ((gop, (h, ps)) :<= prems)) | h == r = cope (do
    let tmpl = TC r [TM x [] | (x, _) <- ps]
    m <- maAM (gop, goal)
    bs <- mayhem $ topSort <$> halfZip ps ss
    m <- argChk m bs
    return [(Our (stan m tmpl) a, stan m prems)]
    )
    (\ _ -> return [])
    return
  backchain _ _ = return []
by goal _ = gripe NotARule

argChk :: Matching -> [((String, Tm), Appl)] -> AM Matching
argChk m [] = return m
argChk m (((x, t), a) : bs) = do
  a@(Our s _) <- scoApplTm (stan m t) a
  argChk ((x, s) : m) bs

invert :: Tm -> AM [((String, [(String, Tm)]), [Tm])]
invert hyp = fold <$> (gamma >>= traverse try )
 where
  try :: CxE -> AM [((String, [(String, Tm)]), [Tm])]
  try (ByRule True ((gop, vok) :<= prems)) = cope (maAM (gop, hyp))
    (\ _ -> return [])
    (\ m -> return [((id *** map (id *** stan m)) vok, stan m prems)])
  try _ = return []

gamma :: AM Context
gamma = AM $ \ setup as -> Right (context as, as)

setGamma :: Context -> AM ()
setGamma ga = AM $ \ setup as -> Right ((), as {context = ga})

fresh :: String -> AM Nom
fresh x = AM $ \ setup as -> case root as of
  (roo, non) -> Right (roo <>> [(x, non)], as {root = (roo, non + 1)})

push :: CxE -> AM ()
push z = AM $ \ setup as -> Right ((), as {context = context as :< z})

pop :: (CxE -> Bool) -> AM (Maybe CxE)
pop test = do
  ga <- gamma
  case go ga of
    Nothing      -> return Nothing
    Just (ga, z) -> setGamma ga >> return (Just z)
 where
  go B0 = Nothing
  go (ga :< z)
    | test z    = Just (ga, z)
    | otherwise = go ga >>= \ (ga, y) -> Just (ga :< z, y)

what's :: String -> AM Syn
what's x = do
  ga <- gamma
  (e, mga) <- go ga
  case mga of
    Nothing -> return ()
    Just ga -> setGamma ga
  return e
 where
  go :: Context -> AM (Syn, Maybe Context)
  go B0 = gripe (Scope x)
  go (_ :< Bind p (User y)) | x == y = return (TP p, Nothing)
  go ga@(_ :< ImplicitQuantifier) = do
    xTp <- (, Hide Type) <$> fresh "Ty"
    xp  <- (, Hide (TE (TP xTp)))  <$> fresh x
    return (TP xp, Just (ga :< Bind xTp Hole :< Bind xp (User x)))
  go (ga :< z) = do
    (e, mga) <- go ga
    return (e, (:< z) <$> mga)

given :: Tm -> AM ()
given goal = gamma >>= go where
  go B0 = gripe NotGiven
  go (ga :< Hyp hyp) = cope (equal (TC "Prop" []) (hyp, goal))
    (\ gr -> go ga) return
  go (ga :< _) = go ga

(|-) :: Tm -> AM x -> AM x
h |- p = do
  push (Hyp h)
  x <- p
  pop $ \case
    Hyp _ -> True
    _ -> False
  return x

scoApplTm :: Tm -> Appl -> AM TmR
scoApplTm ty a@(_, t) = ((`Our` a)) <$> go t
  where
    go :: Appl' -> AM Tm
    go ((t, _, y) :$$ ras) = case t of
      Lid -> do
        (e, sy) <- synApps y ras
        subtype sy ty
        return $ TE e
      _   -> do
        TC d ss <- hnf ty
        (fold <$> (gamma >>= traverse (try d ss y))) >>= \case
          [] -> gripe (DoesNotMake y d)
          _ : _ : _ -> gripe (OverOverload y)
          [(m, as)] -> do
            let tmpl = TC y [TM x [] | (x, _) <- as]
            bs <- cope (mayhem $ topSort <$> halfZip as ras)
                    (\ _ -> gripe (WrongNumOfArgs y))
                    return
            m <- argChk m bs
            return $ stan m tmpl
    try :: Con -> [Tm] -> Con -> CxE -> AM [(Matching, [(String, Tm)])]
    try d ss c ((d', ps) ::> (c', as)) | d == d' && c == c' = do
      m <- concat <$> ((mayhem $ halfZip ps ss) >>= traverse maAM)
      return [(m, as)]
    try _ _ _ _ = return []

synApps :: String -> [Appl] -> AM (Syn, Tm)
synApps f as = do
  f@(TP (_, Hide t)) <- what's f
  spinalApp (f, t) as

spinalApp :: (Syn, Tm) -> [Appl] -> AM (Syn, Tm)
spinalApp fsy [] = return fsy
spinalApp (f, sy) (a : as) = do
  (dom, ran) <- makeFun sy
  Our s _ <- scoApplTm dom a
  spinalApp (f :$ s, ran) as

makeFun :: Tm -> AM (Tm, Tm)
makeFun (TC "->" [dom, ran]) = return (dom, ran)
makeFun _ = gripe FAIL -- could do better

subtype :: Tm -> Tm -> AM ()
subtype got want = unify (got, want)

unify :: (Tm, Tm) -> AM ()
unify (a, b) = do
  a <- hnf a
  b <- hnf b
  True <- track (show a ++ " =? " ++ show b) (return True)
  case (a, b) of
    (TC f as, TC g bs) -> do
      guard $ f == g
      abs <- mayhem $ halfZip as bs
      traverse unify abs
      return ()
    (TE (TP (x, _)), t) -> make x t
    (s, TE (TP (y, _))) -> make y s
    _ -> gripe FAIL

make :: Nom -> Tm -> AM ()
make x (TE (TP (y, _))) | x == y = return ()
make x t = do
  nomBKind x >>= \case
    User _ -> gripe FAIL
    Defn s -> unify (s, t)
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

-- currently a knock-off, this checks that rules are good for props
scoApplRu :: Tm -> Appl -> AM TmR
scoApplRu ty a@(_, t) = ((`Our` a)) <$> go t
  where
    go :: Appl' -> AM Tm
    go ((t, _, y) :$$ ras) = case t of
      Lid -> TE <$> (foldl (:$) <$> what's y <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras

applScoTm :: Tm -> Appl -> AM TmR
applScoTm ty a = do
  push ImplicitQuantifier
  t <- scoApplTm ty a
  pop $ \case
    ImplicitQuantifier -> True
    _ -> False
  return t

nomBKind :: Nom -> AM BKind
nomBKind x = gamma >>= foldl me empty where
  me no (Bind (y, _) bk) | x == y = return bk
  me no _ = no

pattern Type = TC "Type" []
pattern Prop = TC "Prop" []
