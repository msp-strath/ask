------------------------------------------------------------------------------
----------                                                          ----------
----------     Context                                              ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    CPP
  , PatternSynonyms
  , TupleSections
  , LambdaCase
#-}

module Language.Ask.Context where

import Control.Monad
import qualified Control.Monad.Fail as Fail
import qualified Data.Map as M
import Control.Applicative
import Control.Arrow ((***))

import Language.Ask.Bwd
import Language.Ask.Hide
import Language.Ask.Tm
import Language.Ask.Lexing
import Language.Ask.RawAsk

import Debug.Trace

------------------------------------------------------------------------------
--  Contexts
------------------------------------------------------------------------------

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Bool{-proven?-} Tm
  | Bind (Nom, Hide Tm) BKind
  | (Nom, [Pat]) :=: Syn  -- computation rule
  | Declare String Nom Sch
  | Defined String
  | RecShadow String
  | ImplicitQuantifier
  | RefuseQuantification
  | (Con, [Pat]) ::> (Con, Tel)  -- constructor declaration
  | ByRule Bool{- pukka intro?-} Rule
  | Demand Subgoal
  | ExpectBlocker
  | Expect Proglem
  | DoorStop
  | Data
      Con         -- name of data type
      Context     -- constructor declarations
  | Gram
      Con         -- nonterminal symbol
      [[GramBit]] -- productions
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
  | AlreadyDeclared String
  | Scope String
  | ByBadRule String Tm
  | ByAmbiguous String Tm
  | EmptyInductively
  | InductiveHypsDon'tLike Con
  | FromNeedsConnective Appl
  | TestNeedsEq Tm
  | UnderNeedsEq Tm
  | NotGiven Tm
  | NotEqual
  | InfiniteType
  | Terror [LexL] Tm Tm
  | NotARule Appl
  | BadRec String
  | Mardiness
  | NoSizedConstruction
  | NotADataType Tm
  | WrongNumOfArgs Con Int [Appl]
  | DoesNotMake Con Tm
  | OverOverload Con
  | NonCanonicalType Tm Con
  | BadFName String
  | Unification Con Con
  | NotAProd Con [GramBit]
  | ParseNoString
  | ParseNotTheWanted Con
  | ParseNoMake String
  | ParseStubSub
  | Bland String
  | FAIL
  deriving Show


------------------------------------------------------------------------------
--  Mutable AskState -- and Read-Only Setup
------------------------------------------------------------------------------

type Root = (Bwd (String, Int), Int)

data AskState = AskState
  { context  :: Context
  , root     :: Root
  , fixities :: FixityTable
  } deriving Show

type Setup = () -- atavism


------------------------------------------------------------------------------
--  The Ask Monad
------------------------------------------------------------------------------

-- My word is my bond, the only code which needs to know the representation of
-- this very monad is in this very section of this very file.
-- How long until I welch on that?

data AM x = AM {runAM
  :: Setup     -- nowt of consequence
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

guardErr :: Bool -> Gripe -> AM ()
guardErr True _ = return ()
guardErr False err = gripe err

instance Fail.MonadFail AM where
  fail _ = gripe FAIL

instance Alternative AM where
  empty = gripe FAIL
  ma <|> mb = cope ma (const mb) return

cope :: AM x -> (Gripe -> AM y) -> (x -> AM y) -> AM y
cope (AM f) yuk wow = AM $ \ setup as -> case f setup as of
  Left g        -> runAM (yuk g) setup as
  Right (x, as) -> runAM (wow x) setup as

getFixities :: AM FixityTable
getFixities = AM $ \ _ s -> Right (fixities s, s)

setFixities :: FixityTable -> AM ()
setFixities ft = AM $ \ _ s -> Right ((), s {fixities = ft})

fixity :: String -> AM (Int, Assocy)
fixity o = do
  ft <- getFixities
  return $ case M.lookup o ft of
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
what's :: String -> AM (Either (Nom, Sch) (Syn, Tm))
what's x = do
  ga <- gamma
  cope (go ga)
    (\case
      Scope _ -> do
        (e, ga) <- qu ga
        setGamma ga
        return e
      gr -> gripe gr)
    $ return
 where
  go :: Context -> AM (Either (Nom, Sch) (Syn, Tm))
  go B0 = gripe (Scope x)
  go (_ :< Bind p@(_, Hide ty) (User y)) | x == y =
    return $ Right (TP p, ty)
  go (ga :< RecShadow y) | x == y = gripe (BadRec x)
  go (ga :< Declare y yn sch) | x == y = return $ Left (yn, sch)
  go (ga :< z) = go ga
--  decl (ga :< Declare y yn sch) | x == y = Just (yn, sch)
--  decl (ga :< _) = decl ga
--  decl B0 = Nothing
  qu ga@(_ :< RefuseQuantification) = gripe (Scope x)
  qu ga@(_ :< ImplicitQuantifier) = do
    xTp <- (, Hide Type) <$> fresh "Ty"
    let xTy = TE (TP xTp)
    xp  <- (, Hide xTy)  <$> fresh x
    return (Right (TP xp, xTy), ga :< Bind xTp Hole :< Bind xp (User x))
  qu B0 = gripe (Scope x)
  qu (ga :< z) = do
    (e, ga) <- qu ga
    return (e, ga :< z)

-- finding one of ours
nomBKind :: Nom -> AM BKind
nomBKind x = gamma >>= foldl me empty where
  me no (Bind (y, _) bk) | x == y = return bk
  me no _ = no

-- wildly incomplete
instance Stan CxE where
  stan ms (Bind (x, Hide ty) k) =
    Bind (x, Hide (stan ms ty)) (stan ms k)
  stan ms z = z
  sbst u es (Bind (x, Hide ty) k) =
    Bind (x, Hide (sbst u es ty)) (sbst u es k)
  sbst u es z = z
  abst x i (Bind (n, Hide ty) k) =
    Bind <$> ((n,) <$> (Hide <$> abst x i ty)) <*> abst x i k
  abst x i z = pure z

instance Stan BKind where
  stan ms (Defn t) = Defn (stan ms t)
  stan _ k = k
  sbst u es (Defn t) = Defn (sbst u es t)
  sbst _ _ k = k
  abst x i (Defn t) = Defn <$> abst x i t
  abst _ _ k = pure k


------------------------------------------------------------------------------
--  Demanding!
------------------------------------------------------------------------------

demand :: Subgoal -> AM ()
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


------------------------------------------------------------------------------
--  Programming Problems
------------------------------------------------------------------------------

data Proglem = Proglem
  { localCx  :: Context
  , fNom     :: Nom
  , uName    :: String
  , leftImpl :: [(Tm, Tm)] -- term-type pairs for implicit arguments
  , leftSatu :: [(Tm, Tm)] -- ditto scheme arguments
  , leftAppl :: [(Tm, Tm)] -- ditto for application arguments
  , rightTy  :: Tm         -- return type
  } deriving Show
