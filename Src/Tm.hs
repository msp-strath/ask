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
import Data.List
import Control.Applicative
import Control.Arrow ((***))

import Ask.Src.Thin
import Ask.Src.HalfZip
import Ask.Src.Hide


------------------------------------------------------------------------------
--  Representation of Terms
------------------------------------------------------------------------------

type Tm = Chk Syn

data Chk s
  = TM String [s]       -- metavariable instantiation
  | TC Con [Chk s]      -- canonical form
  | TB (Bind (Chk s))   -- binding form
  | TE s                -- other stuff
  deriving (Eq, Show, Functor, Foldable, Traversable)

data Syn
  = TV Int              -- de Bruijn index
  | TP (Nom, Hide Tm)   -- named var, with cached type
  | Tm ::: Tm           -- radical
  | Syn :$ Tm           -- elimination
  deriving (Show, Eq)

data Bind b
  = K{-onstant-} b
  | L{-ambda-}   b
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Con = String            -- canonical constructors get to be plain names
-- these are a few of our favourite things
pattern Type      = TC "Type" []
pattern Prop      = TC "Prop" []
pattern TRUE      = TC "True" []
pattern FALSE     = TC "False" []
pattern (:->) s t = TC "->" [s, t]

type Nom = [(String, Int)]   -- names for parameters are chosen by the system


------------------------------------------------------------------------------
--  Patterns
------------------------------------------------------------------------------

data Pat
  = PM String Thinning     -- metavariable binding site
  | PC Con [Pat]           -- canonical pattern
  | PB Pat                 -- binding pattern
  deriving (Show, Eq)


------------------------------------------------------------------------------
--  Telescopes, used to give types for constructor argument vectors
------------------------------------------------------------------------------

data Tel
  = Ex Tm (Bind Tel)       -- implicit existential
  | (String, Tm) :*: Tel   -- named explicit fields
  | Pr Tm                  -- proof obligation, e.g., TRUE
  deriving Show
infixr 6 :*:


------------------------------------------------------------------------------
--  Subgoals
------------------------------------------------------------------------------

data Subgoal
  = PROVE Tm          -- of type Prop
  | GIVEN Tm Subgoal  -- the hyp is a Prop
  -- more to follow, no doubt
  deriving Show


------------------------------------------------------------------------------
--  Thin all the Things
------------------------------------------------------------------------------

instance Thin s => Thin (Chk s) where
  TM m ss <^> th = TM m (ss <^> th)
  TC c ts <^> th = TC c (ts <^> th)
  TB t    <^> th = TB (t <^> th)
  TE s    <^> th = TE (s <^> th)
  thicken th (TM m ss) = TM m <$> thicken th ss
  thicken th (TC c ts) = TC c <$> thicken th ts
  thicken th (TB t)    = TB <$> thicken th t
  thicken th (TE s)    = TE <$> thicken th s
  
instance Thin Syn where
  TV i <^> th = TV (i <^> th)
  (t ::: _T) <^> th = (t <^> th) ::: (_T <^> th)
  (e :$ s) <^> th = (e <^> th) :$ (s <^> th)
  TP x <^> th = TP x
  thicken th (TV i) = TV <$> thicken th i
  thicken th (t ::: _T) = (:::) <$> thicken th t <*> thicken th _T
  thicken th (e :$ s) = (:$) <$> thicken th e <*> thicken th s
  thicken th (TP x) = pure (TP x)

instance Thin s => Thin (Bind s) where
  K s <^> th = K (s <^> th)
  L s <^> th = L (s <^> os th)
  thicken th (K s) = K <$> thicken th s
  thicken th (L s) = L <$> thicken (os th) s

instance Thin s => Thin [s] where
  ss <^> th = fmap (<^> th) ss
  thicken th ss = traverse (thicken th) ss

instance Thin Tel where
  Ex s b         <^> th = Ex (s <^> th) (b <^> th)
  ((x, s) :*: t) <^> th = (x, s <^> th) :*: (t <^> th)
  Pr p           <^> th = Pr (p <^> th)
  thicken th (Ex s b)       = Ex <$> thicken th s <*> thicken th b
  thicken th ((x, s) :*: t) = (:*:) <$> ((x,) <$> thicken th s) <*> thicken th t
  thicken th (Pr p)         = Pr <$> thicken th p

instance Thin Subgoal where
  PROVE g   <^> th = PROVE (g <^> th)
  GIVEN h g <^> th = GIVEN (h <^> th) (g <^> th)
  thicken th (PROVE g)   = PROVE <$> thicken th g
  thicken th (GIVEN h g) = GIVEN <$> thicken th h <*> thicken th g

instance Thin () where _ <^> _ = () ; thicken _ _ = Just ()


------------------------------------------------------------------------------
--  Metavariable Matchings, instantiation, substitution
------------------------------------------------------------------------------

type Matching = [(String, Chk Syn)]

class Stan t where
  stan :: Matching
       -> t -> t
  sbst :: Int -> [Syn]
       -> t -> t

-- yer ordinary rhythm'n'blues, yer basic rock'n'roll
(//) :: Stan t => Bind t -> Syn -> t
K t // e = t
L t // e = sbst 0 [e] t

upTE :: Syn -> Tm
upTE (t ::: _) = t
upTE e = TE e

instance Stan s => Stan [s] where
  stan ms = fmap (stan ms)
  sbst u es = fmap (sbst u es)

instance (Stan s, Stan t) => Stan (s, t) where
  stan ms = stan ms *** stan ms
  sbst u es = sbst u es *** sbst u es

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

instance Stan Tel where
  stan ms (Ex s b)       = Ex (stan ms s) (stan ms b)
  stan ms ((x, s) :*: t) = (x, stan ms s) :*: stan ms t
  stan ms (Pr p)         = Pr (stan ms p)
  sbst u es (Ex s b)       = Ex (sbst u es s) (sbst u es b)
  sbst u es ((x, s) :*: t) = (x, sbst u es s) :*: sbst u es t
  sbst u es (Pr p)         = Pr (sbst u es p)

instance Stan Subgoal where
  stan ms (PROVE g)   = PROVE (stan ms g)
  stan ms (GIVEN h g) = GIVEN (stan ms h) (stan ms g)
  sbst u es (PROVE g)   = PROVE (sbst u es g)
  sbst u es (GIVEN h g) = GIVEN (sbst u es h) (sbst u es g)

instance Stan () where stan _ _ = () ; sbst _ _ _ = ()


------------------------------------------------------------------------------
--  Metavariable dependency testing and topological insertion
------------------------------------------------------------------------------

class MDep t where
  mDep :: String -> t -> Bool

instance MDep Tm where
  mDep x (TM m es) = m == x || mDep x es
  mDep x (TC _ ts) = mDep x ts
  mDep x (TB t) = mDep x t
  mDep x (TE e) = mDep x e

instance MDep Syn where
  mDep x (t ::: ty) = mDep x t || mDep x ty
  mDep x (f :$ s) = mDep x f || mDep x s
  mDep x _ = False

instance MDep x => MDep [x] where
  mDep x = any (mDep x)

instance MDep b => MDep (Bind b) where
  mDep x (K t) = mDep x t
  mDep x (L t) = mDep x t

topInsert :: MDep t =>
  ((String, t), z) -> [((String, t), z)] -> [((String, t), z)]
topInsert b [] = [b]
topInsert b@((x, _), _) (a@((_, t), _) : bs)
    | mDep x t = b : a : bs
    | otherwise = a : topInsert b bs
