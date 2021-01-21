{-# LANGUAGE CPP, TupleSections #-}
module Ask.Src.Scoping where

import Data.List
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Applicative
import qualified Data.Map as M

import Ask.Src.Bwd
import Ask.Src.Thin
import Ask.Src.HalfZip
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing

data Gripe
  = Surplus
  | Scope String
  | ByBadRule
  | NotGiven
  | NotEqual
  | ByAmbiguous
  | Mardiness
  | BadSubgoal
  | FAIL
  deriving (Show, Eq)

data AM x = AM {runAM
  :: Setup    -- rules and stuff
  -> Context  -- vars and hyps
  -> Either Gripe x}

instance Monad AM where
  return x    = AM $ \ _ _ -> Right x
  AM f >>= k = AM $ \ setup ga -> case f setup ga of
    Left g -> Left g
    Right x -> runAM (k x) setup ga
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
cope (AM f) yuk wow = AM $ \ setup ga -> case f setup ga of
  Left g  -> runAM (yuk g) setup ga
  Right x -> runAM (wow x) setup ga

instance Alternative AM where
  empty = gripe FAIL
  ma <|> mb = cope ma (const mb) return

data Setup = Setup
  { introRules :: [Rule]
  , weirdRules :: [Rule]
  , fixities   :: FixityTable
  } deriving Show

fixity :: String -> AM (Int, Assocy)
fixity o = AM $ \ s _ -> Right $ case M.lookup o (fixities s) of
  Nothing -> (9, LAsso)
  Just x  -> x

hnf :: Tm -> AM Tm
hnf = return -- not for long

equal :: Tm -> (Tm, Tm) -> AM ()
equal ty (x, y) = guard $ x == y -- not for long

maAM :: Pat -> Tm -> AM Matching
maAM p t = go mempty (p, t) where
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

data Rule =
  (Pat, Pat) :<=
  [ Tm
  ]
  deriving Show

by :: Tm -> Tm -> AM [Tm]
by goal invok = do
  byrs <- AM $ \ s _ -> Right (introRules s ++ weirdRules s)
  subses <- concat <$> traverse backchain byrs
  case subses of
    [subs] -> return subs
    []     -> gripe ByBadRule
    _      -> gripe ByAmbiguous
 where
  backchain :: Rule -> AM [[Tm]] -- list of successes
  backchain ((gop, rup) :<= prems) = cope
    ((++) <$> maAM gop goal <*> maAM rup invok)
    (\ _ -> return [])
    (\ m -> return [stan m prems])

invert :: Tm -> AM [(Pat, [Tm])]
invert hyp = do
  intros <- AM $ \ s _ -> Right (introRules s)
  concat <$> traverse try intros
 where
  try :: Rule -> AM [(Pat, [Tm])]
  try ((gop, rup) :<= prems) = cope (maAM gop hyp)
    (\ _ -> return [])
    (\ m -> return [(rup, stan m prems)])

type Context = Bwd CxE

what's :: String -> AM Syn
what's x = AM $ \ setup ga -> TV <$> go 0 ga where
  go i B0 = Left (Scope x)
  go i (ga :< Var y) = if x == y then Right 0 else (1 +) <$> go i ga
  go i (ga :< _)     = go i ga

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String  -- dear god no, fix this to be locally nameless
  deriving (Show, Eq)

given :: Tm -> AM ()
given goal = AM (\ _ ga -> Right ga) >>= go where
  go B0 = gripe NotGiven
  go (ga :< Hyp hyp) = cope (equal (TC "Prop" []) (hyp, goal))
    (\ gr -> go ga) return
  go (ga :< _) = go ga

(|-) :: CxE -> AM x -> AM x
e |- p = AM $ \ setup ga -> runAM p setup (ga :< e)

applScoTm :: Appl -> (Context, TmR)
applScoTm a@(_, x) = (ga, Our t a) where
  (xs, t) = go x
  ga = B0 <>< map Var (nub xs)
  ge x (ga :< Var y) = if x == y then 0 else 1 + ge x ga
  ge x (ga :< _)     = ge x ga
  go ((t, _, y) :$$ ras) = case t of
      Lid -> (y : ys, TE (foldl (:$) (TV (ge y ga)) ts))
      _   -> (ys, TC y ts)
    where
    (ys, ts) = traverse (go . snd) ras

scoApplTm :: Appl -> AM TmR
scoApplTm a@(_, t) = ((`Our` a)) <$> go t
  where
    go :: Appl' -> AM Tm
    go ((t, _, y) :$$ ras) = case t of
      Lid -> TE <$> (foldl (:$) <$> what's y <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras
