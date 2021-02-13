------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Tm                                           ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    TupleSections
  , DeriveTraversable
  , TypeSynonymInstances
  , FlexibleInstances
  , PatternSynonyms
#-}

module Ask.Src.Tm where

import Data.Bits
import Data.List hiding ((\\))
import Control.Applicative
import Control.Arrow ((***))
import Data.Monoid
import Control.Monad.Writer
import Control.Monad.Identity
import qualified Data.Set as S
import qualified Data.Map as M

import Ask.Src.Bwd
import Ask.Src.Thin
import Ask.Src.HalfZip
import Ask.Src.Hide


------------------------------------------------------------------------------
--  Representation of Terms
------------------------------------------------------------------------------

type Tm = Chk  -- terms
type Ty = Chk  -- types
type Pr = Chk  -- propositions

data Chk
  = TC Con [Chk]    -- canonical form
  | TB (Bind Chk)   -- binding form
  | TE Syn          -- other stuff
  deriving (Eq, Show)

data Syn
  = TV Int              -- de Bruijn index
  | TP Decl             -- named var, with cached type
  | Tm ::: Ty           -- radical
  | Syn :$ Tm           -- elimination
  deriving (Show, Eq)

data Bind b
  = K{-onstant-} b
  | L{-ambda-}   b
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Con = String            -- canonical constructors get to be plain names

data Decl = Decl
  { nom :: Nom
  , typ :: Ty
  , wot :: Colour
  , who :: Maybe (String, Tel Ty)
  }
instance Show Decl where
  show d = show (nom d) ++ "(" ++ show (wot d) ++ ")"
instance Eq  Decl where d == e = nom d == nom e
instance Ord Decl where compare d e = compare (nom d) (nom e)

data Colour
  = Purple
  | Orange
  | Green Bool{-complete?-} Syn
  | Brown
  deriving Show
  
stableColour :: Colour -> Bool
stableColour Orange      = False
stableColour (Green b _) = b
stableColour _           = True

green :: Syn -> Colour
green e = Green (stable e) e

-- these are a few of our favourite things
pattern Type      = TC "Type" []
pattern Prop      = TC "Prop" []
pattern TRUE      = TC "True" []
pattern FALSE     = TC "False" []
pattern (:->) s t = TC "->" [s, t]
pattern Zone      = TC "$$" []  -- a type which gets hypothetically inhabited
pattern Sigma a b = TC "'Sigma" [a, TB b]
pattern Pair s t  = TC "(,)" [s, t]
pattern Fst       = TC "Fst" []
pattern Snd       = TC "Snd" []
pattern Sub s t   = TC "'<=" [s, t]
pattern Q ty l r  = TC "=" [ty, l, r]

type Nom = [(String, Int)]   -- names for parameters are chosen by the system


------------------------------------------------------------------------------
--  Subgoals
------------------------------------------------------------------------------

type Subgoal = Chk
pattern PROVE p   = TC "prove" [p]
pattern GIVEN h g = TC "given" [h, g]


------------------------------------------------------------------------------
--  Mangling
------------------------------------------------------------------------------

data Mangling f = Mangling
  { mangV :: Int  -> f Syn    -- how to treat the de Bruijnies
  , mangP :: Decl -> f Syn    -- how to treat the nominees
  , mangL :: Mangling f       -- how to go under a binder
  }

class Mangle t where
  mangle :: Applicative f => Mangling f -> t -> f t

mingle :: Mangle t => Mangling Identity -> t -> t
mingle m = runIdentity . mangle m

instance Mangle t => Mangle (Bind t) where
  mangle m (K t) = K <$> mangle m t
  mangle m (L t) = L <$> mangle (mangL m) t

instance Mangle Syn where
  mangle m (TV i)    = mangV m i
  mangle m (TP d)    = mangP m d
  mangle m (f :$ s)  = (:$) <$> mangle m f <*> mangle m s
  mangle m (t ::: u) = (:::) <$> mangle m t <*> mangle m u

instance Mangle Chk where
  mangle m (TC c ts) = TC c <$> mangle m ts
  mangle m (TB b)    = TB <$> mangle m b
  mangle m (TE e)    = TE <$> mangle m e

instance Mangle t => Mangle [t] where
  mangle = traverse . mangle

instance Mangle t => Mangle (Bwd t) where
  mangle = traverse . mangle

instance (Mangle s, Mangle t) => Mangle (s, t) where
  mangle m (s, t) = (,) <$> mangle m s <*> mangle m t

instance Mangle Bool where
  mangle _ = pure

instance Mangle Decl where
  mangle m (Decl nom ty wot who) =
    Decl nom <$> mangle m ty <*> mangle m wot <*> pure who

instance Mangle Colour where
  mangle m (Green b tm) = green <$> mangle m tm
  mangle m c = pure c
  

------------------------------------------------------------------------------
--  Thin all the Things
------------------------------------------------------------------------------

thinMang :: Thinning -> Mangling Identity
thinMang th = Mangling
  { mangV = \ i -> pure $ TV (i <^> th)
  , mangP = \ d -> pure $ TP d
  , mangL = thinMang (os th)
  }

thickMang :: Thinning -> Mangling Maybe
thickMang th = Mangling
  { mangV = \ i -> TV <$> thicken th i
  , mangP = \ d -> pure $ TP d
  , mangL = thickMang (os th)
  }

instance Thin Chk where
  t <^> th     = mingle (thinMang th) t
  thicken th t = mangle (thickMang th) t

instance Thin Syn where
  t <^> th     = mingle (thinMang th) t
  thicken th t = mangle (thickMang th) t


------------------------------------------------------------------------------
--  Substitution and Abstraction
------------------------------------------------------------------------------

substMang :: Bwd Syn  -- V-closed terms to substitute for Vs...
          -> Int      -- ...starting with this one
          -> Mangling Identity
substMang ez u = Mangling
  { mangV = \ i -> let j = i - u in if j < 0
     then pure $ TV i
     else case ez <? j of
       Right e -> pure e
       Left k  -> pure $ TV (k + u)
  , mangP = \ d -> pure $ TP d
  , mangL = substMang ez (u + 1)
  }

sbst :: Mangle t => Bwd Syn -> t -> t
sbst ez = mingle $ substMang ez 0

(//) :: Mangle t => Bind t -> Syn -> t
K t // _ = t
L t // e = sbst (B0 :< e) t

abstMang :: Bwd Nom  -- names to make de Bruijn...
         -> Int      -- ...starting here
         -> Mangling (Writer Any)
abstMang nz u = Mangling
  { mangV = \ i -> pure $ TV i
  , mangP = \ d -> case wherez (nom d ==) nz of
      Just i  -> TV (i + u) <$ tell (Any True)
      Nothing -> pure $ TP d
  , mangL = abstMang nz (u + 1)
  }

(\\) :: Mangle t => Nom -> t -> Bind t
x \\ t = if b then L t' else K t
  where (t', Any b) = runWriter $ mangle (abstMang (B0 :< x) 0) t


------------------------------------------------------------------------------
--  Support
------------------------------------------------------------------------------

suppMang :: Mangling (Const (S.Set Decl))
suppMang = Mangling
  { mangV = const $ Const mempty
  , mangP = Const . S.singleton
  , mangL = suppMang
  }

support :: Mangle t => t -> S.Set Decl
support = getConst . mangle suppMang

stable :: Mangle t => t -> Bool
stable = all (stableColour . wot) . support

-- not the finest dep-check known to humanity
dep :: Mangle t => Decl -> t -> Bool
dep x = any (x ==) . support 


------------------------------------------------------------------------------
--  News
------------------------------------------------------------------------------

newtype News = News {news :: M.Map Nom Decl} deriving Show

newsMang :: News -> Mangling (Writer Any)
newsMang (News n) = m where
  m = Mangling
    { mangV = \ i -> pure (TV i)
    , mangP = \ d -> case M.lookup (nom d) n of
        Just d -> TP d <$ tell (Any True)
        Nothing -> pure (TP d)
    , mangL = m
    }

update :: Mangle t => News -> t -> t
update n t = t' where
  (t' , _) = runWriter $ mangle (newsMang n) t

(%=) :: Nom -> Decl -> News
x %= d = News $ M.singleton x d

instance Mangle News where
  mangle m (News news) = News <$> traverse (mangle m) news

instance Monoid News where
  mempty = News $ M.empty
  mappend n@(News newer) (News older) =
    News $ newer <> older'
    where
    News older' = update n (News (M.difference older newer))
instance Semigroup News where (<>) = mappend

(><) :: News -> News -> News
News a >< News b = News (a <> b)


------------------------------------------------------------------------------
--  Telescopes
------------------------------------------------------------------------------

-- Telescopes are a term monad for programs which consume lists of payload...
-- ...but there's a twist.

type Tel x = Chk

pattern Sg x s b = TC "'Sg" [x, s, TB b]
  -- where x is one of
pattern Impl s b = Sg (TC "Impl" []) s b
pattern Expl s b = Sg (TC "Expl" []) s b

pattern Pr p t = TC "'Pr" [p, t]     -- proof obligation
pattern Re x   = TC "'Re" [x]        -- return

pattern Ok = TC "()" []