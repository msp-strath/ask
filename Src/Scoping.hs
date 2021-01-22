{-# LANGUAGE CPP, TupleSections, LambdaCase, PatternSynonyms #-}
module Ask.Src.Scoping where

import Data.List
import Control.Monad
import qualified Control.Monad.Fail as Fail
import Control.Applicative
import qualified Data.Map as M
import Data.Foldable
import Control.Arrow ((***))

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
  | FromNeedsConnective
  | NotGiven
  | NotEqual
  | NotARule
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
  (Pat, (String, [(Con, Tm)])) :<=
  [ Tm
  ]
  deriving (Show, Eq)

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
    m <- maAM gop goal
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
  try (ByRule True ((gop, vok) :<= prems)) = cope (maAM gop hyp)
    (\ _ -> return [])
    (\ m -> return [((id *** map (id *** stan m)) vok, stan m prems)])
  try _ = return []

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String  -- dear god no, fix this to be locally nameless
  | Bind (Nom, Hide Tm) BKind
  | ImplicitQuantifier
  | ByRule Bool{- pukka intro?-} Rule
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
      Lid -> TE <$> (foldl (:$) <$> what's y <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras

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