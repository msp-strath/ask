------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Context                                      ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    CPP
  , PatternSynonyms
  , TupleSections
#-}

module Ask.Src.Context where

import Control.Monad
import qualified Control.Monad.Fail as Fail
import qualified Data.Map as M
import Control.Applicative
import Control.Arrow ((***))

import Ask.Src.Bwd
import Ask.Src.Hide
import Ask.Src.Tm
import Ask.Src.RawAsk


------------------------------------------------------------------------------
--  Contexts
------------------------------------------------------------------------------

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Bind (Nom, Hide Tm) BKind
  | ImplicitQuantifier
  | (Con, [Pat]) ::> (Con, Tel)
  | ByRule Bool{- pukka intro?-} Rule
  | Demand Subgoal
  | DoorStop
  deriving Show

data BKind
  = User String
  | Defn Tm
  | Hole
  deriving Show

data Rule =
  (Pat, (Con, Tel)) :<=
  [ Subgoal
  ]
  deriving Show


------------------------------------------------------------------------------
--  Gripes
------------------------------------------------------------------------------

data Gripe
  = Surplus
  | Duplication Tm Con
  | Scope String
  | ByBadRule String Tm
  | ByAmbiguous String Tm
  | FromNeedsConnective Appl
  | NotGiven Tm
  | NotEqual
  | NotARule Appl
  | Mardiness
  | WrongNumOfArgs Con Int [Appl]
  | DoesNotMake Con Tm
  | OverOverload Con
  | NonCanonicalType Tm Con
  | FAIL
  deriving Show


------------------------------------------------------------------------------
--  Mutable AskState and Read-Only Setup
------------------------------------------------------------------------------

type Root = (Bwd (String, Int), Int)

data AskState = AskState
  { context :: Context
  , root    :: Root
  } deriving Show

data Setup = Setup
  { fixities   :: FixityTable
  } deriving Show


------------------------------------------------------------------------------
--  The Ask Monad
------------------------------------------------------------------------------

-- My word is my bond, the only code which needs to know the representation of
-- this very monad is in this very section of this very file.
-- How long until I welch on that?

data AM x = AM {runAM
  :: Setup     -- rules and stuff
  -> AskState  -- vars and hyps
  -> Either Gripe (x, AskState)}

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

gripe :: Gripe -> AM x
gripe g = AM $ \ _ _ -> Left g

instance Fail.MonadFail AM where
  fail _ = gripe FAIL

instance Alternative AM where
  empty = gripe FAIL
  ma <|> mb = cope ma (const mb) return

cope :: AM x -> (Gripe -> AM y) -> (x -> AM y) -> AM y
cope (AM f) yuk wow = AM $ \ setup as -> case f setup as of
  Left g        -> runAM (yuk g) setup as
  Right (x, as) -> runAM (wow x) setup as

setup :: AM Setup
setup = AM $ \ setup as -> Right (setup, as)

fixity :: String -> AM (Int, Assocy)
fixity o = do
  s <- setup
  return $ case M.lookup o (fixities s) of
    Nothing -> (9, LAsso)
    Just x  -> x

mayhem :: Maybe x -> AM x
mayhem mx = do
  Just x <- return mx
  return x

gamma :: AM Context
gamma = AM $ \ setup as -> Right (context as, as)

setGamma :: Context -> AM ()
setGamma ga = AM $ \ setup as -> Right ((), as {context = ga})

fresh :: String -> AM Nom
fresh x = AM $ \ setup as -> case root as of
  (roo, non) -> Right (roo <>> [(x, non)], as {root = (roo, non + 1)})


------------------------------------------------------------------------------
--  Context-Wrangling and Fresh Thingy Generation
------------------------------------------------------------------------------

-- imagine a value of a given type
hole :: Tm -> AM Syn
hole ty = do
  x <- fresh "hole"
  let xp = (x, Hide ty)
  push $ Bind xp Hole
  return $ TP xp

-- push a new context entry
push :: CxE -> AM ()
push z = do
  ga <- gamma
  setGamma (ga :< z)

-- remove the topmost entry passing a test, leaving those above in place
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

-- find one of the user's variables by what they call it
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

-- finding one of ours
nomBKind :: Nom -> AM BKind
nomBKind x = gamma >>= foldl me empty where
  me no (Bind (y, _) bk) | x == y = return bk
  me no _ = no


------------------------------------------------------------------------------
--  Demanding!
------------------------------------------------------------------------------

demand :: Subgoal -> AM ()
demand (PROVE TRUE) = return ()
demand sg = push (Demand sg)

demands :: AM [Subgoal]
demands = do
  ga <- gamma
  let (ga', ss) = go ga []
  setGamma ga'
  return ss
 where
  go B0 ss = (B0, ss)
  go (ga :< Demand s) ss = go ga (s : ss)
  go (ga :< z) ss = ((:< z) *** id) (go ga ss)


------------------------------------------------------------------------------
--  DoorStop
------------------------------------------------------------------------------

-- these should bracket

doorStop :: AM ()
doorStop = push DoorStop

doorStep :: AM [CxE]
doorStep = do
  ga <- gamma
  let (ga', de) = go ga []
  setGamma ga'
  return de
 where
  go (ga :< DoorStop) de = (ga, de)
  go (ga :< z)        de = go ga (z : de)
  go B0               de = (B0, de)       -- heaven forfend

pushOutDoor :: CxE -> AM ()
pushOutDoor x = (go <$> gamma) >>= setGamma where
  go B0               = B0 :< x  -- heaven forfend
  go (ga :< DoorStop) = ga :< x :< DoorStop
  go (ga :< z)        = go ga :< z
