{-# LANGUAGE TupleSections
           , DeriveTraversable
           , TypeSynonymInstances
           , FlexibleInstances
#-}

module Ask.Src.Tm where

import Data.Bits
import Data.List
import Control.Applicative

import Ask.Src.Thin
import Ask.Src.HalfZip
import Ask.Src.Hide

type Nom = [(String, Int)]
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
  = TV Int         -- de Bruijn index
  | TP (Nom, Hide Tm)   -- named var, with cached type
  | Tm ::: Tm
  | Syn :$ Tm
  deriving (Show, Eq)

instance Thin Syn where
  TV i <^> th = TV (i <^> th)
  (t ::: _T) <^> th = (t <^> th) ::: (_T <^> th)
  (e :$ s) <^> th = (e <^> th) :$ (s <^> th)
  TP x <^> th = TP x
  thicken th (TV i) = TV <$> thicken th i
  thicken th (t ::: _T) = (:::) <$> thicken th t <*> thicken th _T
  thicken th (e :$ s) = (:$) <$> thicken th e <*> thicken th s
  thicken th (TP x) = pure (TP x)

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

(//) :: Stan t => Bind t -> Syn -> t
K t // e = t
L t // e = sbst 0 [e] t

upTE :: Syn -> Tm
upTE (t ::: _) = t
upTE e = TE e

instance Stan s => Stan [s] where
  stan ms = fmap (stan ms)
  sbst u es = fmap (sbst u es)

instance Stan Syn where
  stan ms (t ::: _T) = stan ms t ::: stan ms _T
  stan ms (e :$ s) = stan ms e :$ stan ms s
  stan ms e = e
  sbst u es (TV i) = sg !! i where
    sg = [TV i | i <- [0 .. (u - 1)]]
         ++ (es <^> Th (shiftL (-1) u)) ++
         [TV i | i <- [u ..]]
  sbst u es (t ::: _T) = sbst u es t ::: sbst u es _T
  sbst u es (e :$ s) = sbst u es e :$ sbst u es s
  sbst u es e = e

instance Stan Tm where
  stan ms (TM m es) = case lookup m ms of
    Just t  -> sbst 0 es' t
    Nothing -> TM m es'
   where
    es' = map (stan ms) es
  stan ms (TC c ts) = TC c (stan ms ts)
  stan ms (TB b)    = TB (stan ms b)
  stan ms (TE e)    = upTE (stan ms e)
  sbst u es (TM m es') = TM m (sbst u es es')
  sbst u es (TC c ts) = TC c (sbst u es ts)
  sbst u es (TB t)    = TB (sbst u es t)
  sbst u es (TE e)    = upTE (sbst u es e)

instance Stan b => Stan (Bind b) where
  stan ms (K b) = K (stan ms b)
  stan ms (L b) = L (stan ms b)
  sbst u es (K b) = K (sbst u es b)
  sbst u es (L b) = L (sbst (u + 1) es b)

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
  sbst u es (TO x) = TO (sbst u es x)
  sbst u es (s :*: t) = sbst u es s :*: sbst u es t

instance Thin () where _ <^> _ = () ; thicken _ _ = Just ()
instance Stan () where stan _ _ = () ; sbst _ _ _ = ()
