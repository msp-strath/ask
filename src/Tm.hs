{-# LANGUAGE TupleSections
           , DeriveTraversable
           , TypeSynonymInstances
           , FlexibleInstances
#-}

module Tm where

import Data.Bits
import Data.List
import Control.Applicative

import Thin
import HalfZip

type Con = String

data Pat
  = PM String Thinning
  | PC Con [Pat]
  | PB Pat
  deriving Show

data Bind b
  = K{-onstant-} b
  | L{-ambda-}   b
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Chk s
  = TM String [s]
  | TC Con [Chk s]
  | TB (Bind (Chk s))
  | TE s
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Tm = Chk Syn

instance Thin s => Thin (Bind s) where
  K s <^> th = K (s <^> th)
  L s <^> th = L (s <^> os th)
  thicken th (K s) = K <$> thicken th s
  thicken th (L s) = L <$> thicken (os th) s

instance Thin s => Thin [s] where
  ss <^> th = fmap (<^> th) ss
  thicken th ss = traverse (thicken th) ss

instance Thin s => Thin (Chk s) where
  TM m ss <^> th = TM m (ss <^> th)
  TC c ts <^> th = TC c (ts <^> th)
  TB t    <^> th = TB (t <^> th)
  TE s    <^> th = TE (s <^> th)
  thicken th (TM m ss) = TM m <$> thicken th ss
  thicken th (TC c ts) = TC c <$> thicken th ts
  thicken th (TB t)    = TB <$> thicken th t
  thicken th (TE s)    = TE <$> thicken th s
  
data Syn
  = TV Int
  deriving (Show, Eq)

instance Thin Syn where
  TV i <^> th = TV (i <^> th)
  thicken th (TV i) = TV <$> thicken th i

match :: Thin s   -- s is almost always Syn, but parametricity matters
      => Thinning -- what thinning maps bound vars in tm to bound vars in pat?
      -> Pat      -- pattern to match against
      -> Chk s    -- term to match
      -> Maybe [(String, Chk s)]
match ph (PM m th) t = ((:[]) . (m,)) <$> thicken th (t <^> ph)
match ph (PC x ps) (TC y ts) | x == y = concat <$> halfZipWith (match ph) ps ts
match ph (PB p) (TB (K t)) = match (o' ph) p t
match ph (PB p) (TB (L t)) = match (os ph) p t
match _ _ _ = Nothing

type Matching = [(String, Chk Syn)]

class Stan t where
  stan :: Matching
       -> t -> t
  sbst :: Int -> [Syn]
       -> t -> t

instance Stan s => Stan [s] where
  stan ms = fmap (stan ms)
  sbst u ss = fmap (sbst u ss)

instance Stan Syn where
  stan _ (TV i) = TV i
  sbst u ss (TV i) = sg !! i where
    sg = [TV i | i <- [0 .. (u - 1)]]
         ++ (ss <^> Th (shiftL (-1) u)) ++
         [TV i | i <- [u ..]]

instance Stan Tm where
  stan ms (TM m ss) = sbst 0 ss' t where
    ss' = map (stan ms) ss
    Just t = lookup m ms
  stan ms (TC c ts) = TC c (stan ms ts)
  stan ms (TB b)    = TB (stan ms b)
  sbst u ss (TM m es) = TM m (sbst u ss es)
  sbst u ss (TC c ts) = TC c (sbst u ss ts)
  sbst u ss (TB t)    = TB (sbst u ss t)
  sbst u ss (TE e)    = TE (sbst u ss e)

instance Stan b => Stan (Bind b) where
  stan ms (K b) = K (stan ms b)
  stan ms (L b) = L (stan ms b)
  sbst u ss (K b) = K (sbst u ss b)
  sbst u ss (L b) = L (sbst (u + 1) ss b)

data Tel x
  = TO x
  | Tm :*: Bind (Tel x)
  deriving Show

instance Thin x => Thin (Tel x) where
  TO x <^> th = TO (x <^> th)
  (s :*: t) <^> th = (s <^> th) :*: (t <^> th)
  thicken th (TO x) = TO <$> thicken th x
  thicken th (s :*: t) = (:*:) <$> thicken th s <*> thicken th t

instance Stan x => Stan (Tel x) where
  stan ms (TO x) = TO (stan ms x)
  stan ms (s :*: t) = stan ms s :*: stan ms t
  sbst u ss (TO x) = TO (sbst u ss x)
  sbst u ss (s :*: t) = sbst u ss s :*: sbst u ss t

instance Thin () where _ <^> _ = () ; thicken _ _ = Just ()
instance Stan () where stan _ _ = () ; sbst _ _ _ = ()
