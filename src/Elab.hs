{-# LANGUAGE PatternSynonyms #-}

module Elab where  -- mothballed for now

import HalfZip
import Bwd
import LexAsk
import Thin
import Tm
import RawAsk

import Control.Monad
import Control.Monad.Fail
import qualified Data.Map as M
import Data.Char

type ElabRules
  = M.Map (String, String) -- (TyCon, VaCon)
          ElabRule

data ElabRule = ElabRule
  { tyConArgs :: [Pat]
  , argElab   :: Tm
  } deriving Show

newtype NameSupply = NS Int
instance Show NameSupply where
  show (NS i) = '?' : show i

nsuc :: NameSupply -> NameSupply
nsuc (NS i) = NS (i + 1)

data Status
  = Block Stumble
  | Defd Tm
  deriving Show

instance Stan Status where
  stan m (Defd t) = Defd (stan m t)
  stan m s        = s
  sbst u es (Defd t) = Defd (sbst u es t)
  sbst u es s        = s

elabRule :: String -> String -> Elab ElabRule
elabRule c k = Elab $ \ ers ga -> case M.lookup (c, k) ers of
  Nothing -> (ga, Left Ouch)
  Just r  -> (ga, Right r)


data Prob
  = Tm :> ([LexL], Appl)
  | Hope Tm
  deriving Show

instance Stan Prob where
  stan m    (_T :> r) = stan m _T :> r
  stan m    (Hope _T) = Hope (stan m _T) 
  sbst u es (_T :> r) = sbst u es _T :> r
  sbst u es (Hope _T) = Hope (sbst u es _T)

must :: Maybe x -> Elab x
must Nothing = stumble Ouch
must (Just x) = return x

type Context = Bwd Entry
data Entry =
  Meta String Prob Status

data Stumble
  = Ouch
  | Await String
  | Dunno
  deriving Show

newtype Elab x = Elab {elab
  :: ElabRules
  -> (Context, NameSupply)
  -> ((Context, NameSupply), Either Stumble x)
  }

instance Monad Elab where
  return x = Elab $ \ ers ga -> (ga, Right x)
  Elab p >>= k = Elab $ \ ers ga -> case p ers ga of
    (ga, Left s) -> (ga, Left s)
    (ga, Right x) -> elab (k x) ers ga
  
elaborate :: Prob -> Elab Tm
elaborate p = Elab $ \ ers ga -> case elab (elaborator p) ers ga of
  (ga, Right t) -> (ga, Right t)
  ((ez, n), Left s) -> let x = show n in
    ((ez :< Meta x p (Block s), nsuc n), Right (TM x []))

stumble :: Stumble -> Elab x
stumble s = Elab $ \ ers ga -> (ga, Left s)

elaborator :: Prob -> Elab Tm
elaborator (TM m _ :> _) = stumble $ Await m
elaborator (TC c ss :> (ls, (_, _, k) :$$ lsas)) | constructory c k = do
  r <- elabRule c k
  m <- must $ concat <$> halfZipWith (match mempty) (tyConArgs r) ss
  TC c <$> elabArgs (stan m (argElab r)) lsas
elaborator _ = stumble Ouch

elabArgs :: Tm -> [([LexL], Appl)] -> Elab [Tm]
elabArgs TDone [] = return []
elabArgs (TArg s t) (lsa : lsas) = do
  x <- elaborate (s :> lsa)
  xs <- elabArgs (t // (x ::: s)) lsas
  return (x : xs)
elabArgs (TInf s t) lsas = do
  x <- elaborate (Hope s)
  xs <- elabArgs (t // (x ::: s)) lsas
  return (x : xs)
elabArgs _ _ = stumble Ouch
  
constructory :: String -> String -> Bool
constructory _ (':' : x) = x /= ":"
constructory _ (c : _) | isAlphaNum c = isUpper c
constructory t _ = t `elem` ["Type", "Prop"]

pattern TDone = TC "Done" []
pattern TArg s t = TC "Arg" [s, TB t]
pattern TInf s t = TC "Exi" [s, TB t]


sineQuaNon :: ElabRules
sineQuaNon = M.fromList
  [ (("Type", "Prop"), ElabRule [] TDone)
  ]

instance Applicative Elab where
  pure = return
  (<*>) = ap

instance Functor Elab where
  fmap = ap . return
