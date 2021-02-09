------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Context                                      ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    CPP
  , PatternSynonyms
  , TupleSections
  , LambdaCase
#-}

module Ask.Src.Context where

import Control.Monad
import qualified Control.Monad.Fail as Fail
import qualified Data.Map as M
import Control.Applicative
import Control.Arrow ((***))
import Data.Foldable

import Ask.Src.OddEven
import Ask.Src.Bwd
import Ask.Src.Hide
import Ask.Src.Tm
import Ask.Src.Lexing
import Ask.Src.RawAsk


------------------------------------------------------------------------------
--  State as Stack
------------------------------------------------------------------------------

type Stack = Bwd Layer

data Layer = Layer
  { myDecl :: Decl
  , myText :: [LexL]
  , myProb :: Elab
  , myNext :: Int
  , myPast :: Bwd Entry
  , myFutu :: [Entry]
  , myNeed :: [Need]
  , myStat :: Status
  } deriving Show

data Need
  = Prove Pr
  deriving Show

data Entry
  = The Layer
  | Gap [LexL]
  | Ctor (Ctor ())
  | Data (Ctor ()) [Ctor ()]
  | Conn (Ctor ()) [Ctor [Subgoal]]
  | Admit Con (Bind (Tel [Subgoal]))
  | ImplicitForall
  | Hyp Pr
  | News News
  deriving Show

data Status = New | Old | Fut deriving Show

data Ctor x = (Con, Con) :- Tel (Tel x) deriving Show
infixr 0 :-

pattern Cons x xs = TC ":" [x, xs]
pattern Nil = TC "[]" []

dummyLayer :: Layer
dummyLayer = Layer
  { myDecl = Decl { nom = [], typ = Prop, wot = Purple, who = Nothing }
  , myText = []
  , myProb = NoElab
  , myNext = 0
  , myPast = B0
  , myFutu = []
  , myNeed = []
  , myStat = Old
  }


------------------------------------------------------------------------------
--  Elaboration Problems
------------------------------------------------------------------------------

data Elab
  = NoElab
  | ElabTop
  | ElabDecl RawDecl
  | ElabStuk Request Elab
  deriving Show

data Request
  = Solve (Bwd Decl) Nom
  deriving Show

instance Mangle Elab where
  mangle m t = pure t


------------------------------------------------------------------------------
--  KickOff
------------------------------------------------------------------------------

startLayer :: Bwd Entry -> Bloc (RawDecl, [LexL]) -> Layer
startLayer lib file = Layer
  { myDecl = Decl
      { nom = []
      , typ = Prop
      , wot = Green True (TRUE ::: Prop)
      , who = Nothing
      }
  , myText = []
  , myProb = ElabTop
  , myNext = length file
  , myPast = lib
  , myFutu = go 0 file
  , myNeed = []
  , myStat = Old
  } where
  go n (g :-/ e) = Gap g : ge n e
  ge n Stop = []
  ge n ((r, ls) :-\ o) = The l : go (n + 1) o where
    l = Layer
      { myDecl = Decl
          {nom = [("decl", n)], typ = Prop, wot = Orange, who = Nothing}
      , myProb = ElabDecl r
      , myText = ls
      , myNext = 0
      , myPast = B0
      , myFutu = []
      , myNeed = []
      , myStat = New
      }
  

------------------------------------------------------------------------------
--  Read-Only Setup
------------------------------------------------------------------------------

data Setup = Setup
  { fixities   :: FixityTable
  } deriving Show


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
  | FromNeedsConnective Appl
  | NotGiven Tm
  | NotEqual
  | NotARule Appl
  | BadRec String
  | Mardiness
  | WrongNumOfArgs Con Int [Appl]
  | ConFail (Con, Con) Int -- should be 0 if we rule out dups properly
  | NonCanonicalType Tm Con
  | BadFName String
  | Conflict Con Con
  | FAIL
  deriving Show


------------------------------------------------------------------------------
--  The Ask Monad
------------------------------------------------------------------------------

data AM x = AM {runAM
  :: Setup
  -> Stack
  -> Either Gripe (x, Stack)}

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

mayhem :: Gripe -> Maybe x -> AM x
mayhem gr mx = case mx of
  Just x -> return x
  _ -> gripe gr

fresh :: String -> AM Nom
fresh x = AM $ \ _ (lz :< l) -> let
  n  = myNext l
  xn = nom (myDecl l) ++ [(x, n)]
  l' = l {myNext = n + 1}
  in  Right (xn, lz :< l')

seek :: (Entry -> Bool) -> AM (Bwd Entry)
seek p = AM $ \ _ lz -> Right (foldMap go lz, lz) where
  go l = foldMap test (myPast l)
  test e = if p e then B0 :< e else B0

problem :: AM Elab
problem = AM $ \ _ lz@(_ :< l) -> Right (myProb l, lz)

push :: Entry -> AM ()
push e = AM $ \ _ (lz :< l) -> Right ((), lz :< l {myPast = myPast l :< e})

prep :: Entry -> AM ()
prep e = AM $ \ _ (lz :< l) -> Right ((), lz :< l {myFutu = e : myFutu l})

-- remove the topmost *local* entry passing a test, leaving those above in place
pop :: (Entry -> Bool) -> AM (Maybe Entry)
pop test = AM $ \ _ old@(lz :< l) -> case go (myPast l) of
  Nothing -> Right (Nothing, old)
  Just (ga', e) ->
    Right (Just e, lz :< l {myPast = ga'})
 where
  go B0 = Nothing
  go (ga :< z)
    | test z    = Just (ga, z)
    | otherwise = ((:< z) *** id) <$> go ga



------------------------------------------------------------------------------
--  Constructor Lookup
------------------------------------------------------------------------------

con :: (String, String) -> AM (Tel (Tel ()))
con dc = do
  ez <- seek $ \case
    Ctor _   -> True
    Data _ _ -> True
    Conn _ _ -> True
    _ -> False
  case foldMap cand ez of
    [tel] -> return tel
    cs -> gripe $ ConFail dc (length cs)
 where
  ct :: Ctor () -> [Tel (Tel ())]
  ct (h :- tel)
    | h == dc = [tel]
    | otherwise = []
  cand :: Entry -> [Tel (Tel ())]
  cand (Ctor x) = ct x
  cand (Data x xs) = foldMap ct (x : xs)
  cand (Conn x _) = ct x
  cand _ = []


------------------------------------------------------------------------------
--  Context-Wrangling and Fresh Thingy Generation
------------------------------------------------------------------------------

-- imagine a value of a given type
hole :: String -> Tm -> AM Syn
hole x ty = do
  x <- fresh x
  let xd = Decl
         { nom = x
         , typ = ty
         , wot = Orange
         , who = Nothing
         }
  let xl = dummyLayer { myDecl = xd, myStat = New }
  push $ The xl
  return $ TP xd

(|-) :: Mangle t => (Maybe (String, Tel Ty), Ty) -> (Syn -> AM t) -> AM (Bind t)
(mu, ty) |- k = do
  x <- fresh (fold (fst <$> mu))
  let xd = Decl { nom = x, typ = ty, wot = Purple, who = mu }
  let xl = dummyLayer { myDecl = xd }
  push (The xl)
  t <- k (TP xd)
  pop $ \case { The l | myDecl l == xd -> True ; _ -> False }
  return $ x \\ t



{-
------------------------------------------------------------------------------
--  Contexts
------------------------------------------------------------------------------

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Bind Decl
--  | (Nom, [Pat]) :=: Syn  -- computation rule
--  | Declare String Nom Sch
  | RecShadow String
  | ImplicitQuantifier
  | (Con, Con) ::> Tel (Tel ())
--  | ByRule Bool{- pukka intro?-} Rule
  | Demand Subgoal
  | ExpectBlocker
  | Expect Proglem
  | DoorStop
  | Data
      Con         -- name of data type
      Context     -- constructor declarations
  deriving Show

{-
data Rule =
  (Pat, (Con, Tel)) :<=
  [ Subgoal
  ]
  deriving Show
-}



{-
-- find one of the user's variables by what they call it
what's :: String -> AM (Either (Nom, Sch) (Syn, Tm))
what's x = do
  ga <- gamma
  (e, mga) <- go ga
  case mga of
    Nothing -> return ()
    Just ga -> setGamma ga
  return e
 where
  go :: Context -> AM (Either (Nom, Sch) (Syn, Tm), Maybe Context)
  go B0 = gripe (Scope x)
  go (_ :< Bind p@(_, Hide ty) (User y)) | x == y =
    return (Right (TP p, ty), Nothing)
  go ga@(_ :< ImplicitQuantifier) = case decl ga of
    Just nsch -> return (Left nsch, Nothing)
    Nothing -> do
      xTp <- (, Hide Type) <$> fresh "Ty"
      let xTy = TE (TP xTp)
      xp  <- (, Hide xTy)  <$> fresh x
      return (Right (TP xp, xTy), Just (ga :< Bind xTp Hole :< Bind xp (User x)))
  go (ga :< RecShadow y) | x == y = gripe (BadRec x)
  go (ga :< Declare y yn sch) | x == y = return (Left (yn, sch), Nothing)
  go (ga :< z) = do
    (e, mga) <- go ga
    return (e, (:< z) <$> mga)
  decl (ga :< Declare y yn sch) | x == y = Just (yn, sch)
  decl (ga :< _) = decl ga
  decl B0 = Nothing
-}

-- finding one of ours
nomDecl :: Nom -> AM Decl
nomDecl x = gamma >>= foldl me empty where
  me no (Bind d) | x == nom d = return d
  me no _ = no


------------------------------------------------------------------------------
--  Constructors
------------------------------------------------------------------------------

con ::
  ( Con -- type constructor
  , Con -- value constructor
  ) -> AM (Tel   -- the tel which eats the type constructor's args to get...
            (Tel   -- ...the tel which eats the value constructor's args to...
              ()))   -- win
con dc = (foldMap try <$> gamma) >>= \case
  [tel] -> return tel
  z     -> gripe $ ConFail dc (length z)
 where
  try (h ::> t) | dc == h = [t]
  try (Data _ ga) = foldMap try ga
  try _ = []
  

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

-}