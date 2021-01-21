{-# LANGUAGE CPP, TupleSections, LambdaCase #-}
module Ask.Src.Scoping where

import Data.List
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Applicative
import qualified Data.Map as M

import Ask.Src.Bwd
import Ask.Src.Thin
import Ask.Src.Hide
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
  { introRules :: [Rule]
  , weirdRules :: [Rule]
  , fixities   :: FixityTable
  } deriving Show

fixity :: String -> AM (Int, Assocy)
fixity o = AM $ \ s as -> Right . (, as) $ case M.lookup o (fixities s) of
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
  byrs <- AM $ \ s as -> Right (introRules s ++ weirdRules s, as)
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
  intros <- AM $ \ s as -> Right (introRules s, as)
  concat <$> traverse try intros
 where
  try :: Rule -> AM [(Pat, [Tm])]
  try ((gop, rup) :<= prems) = cope (maAM gop hyp)
    (\ _ -> return [])
    (\ m -> return [(rup, stan m prems)])

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String  -- dear god no, fix this to be locally nameless
  | Bind (Nom, Hide Tm) BKind
  | ImplicitQuantifier
  deriving (Show, Eq) -- get rid of that Eq!

data BKind
  = User String
  | Defn Tm
  | Hole
  deriving (Show, Eq)

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
    xTp <- (, Hide (TC "Type" [])) <$> fresh "Ty"
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

scoApplTm :: Appl -> AM TmR
scoApplTm a@(_, t) = ((`Our` a)) <$> go t
  where
    go :: Appl' -> AM Tm
    go ((t, _, y) :$$ ras) = case t of
      Lid -> TE <$> (foldl (:$) <$> what's y <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras

applScoTm :: Appl -> AM TmR
applScoTm a = do
  push ImplicitQuantifier
  t <- scoApplTm a
  pop $ \case
    ImplicitQuantifier -> True
    _ -> False
  return t

nomBKind :: Nom -> AM BKind
nomBKind x = gamma >>= foldl me empty where
  me no (Bind (y, _) bk) | x == y = return bk
  me no _ = no