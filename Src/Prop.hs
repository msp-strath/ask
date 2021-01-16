{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TupleSections, FlexibleInstances, PatternGuards #-}

module Prop where

import Data.Bits
import Data.List
import Control.Applicative

import Thin

--newtype Con = Con String deriving (Show, Eq)
type Con = String

data Pat
  = PM String Thinning
  | PC Con [Pat]
  | PB Pat
  deriving Show

data Chk s
  = TM String [s]
  | TC Con [Chk s]
  | TB (Chk s)
  | TE s
  deriving (Eq, Show, Functor, Foldable, Traversable)

type Tm = Chk Syn

instance Thin s => Thin [s] where
  ss <^> th = fmap (<^> th) ss
  thicken th ss = traverse (thicken th) ss

instance Thin s => Thin (Chk s) where
  TM m ss <^> th = TM m (ss <^> th)
  TC c ts <^> th = TC c (ts <^> th)
  TB t    <^> th = TB (t <^> os th)
  TE s    <^> th = TE (s <^> th)
  thicken th (TM m ss) = TM m <$> thicken th ss
  thicken th (TC c ts) = TC c <$> thicken th ts
  thicken th (TB t)    = TB <$> thicken (os th) t
  thicken th (TE s)    = TE <$> thicken th s
  
data Syn
  = TV Int
  deriving (Show, Eq)

instance Thin Syn where
  TV i <^> th = TV (i <^> th)
  thicken th (TV i) = TV <$> thicken th i

match :: Thin s => Pat -> Chk s -> Maybe [(String, Chk s)]
match (PM m th) t = ((:[]) . (m,)) <$> thicken th t
match (PC x ps) (TC y ts) | x == y = concat <$> halfZipWith match ps ts
match (PB p) (TB t) = match p t
match _ _ = Nothing

class HalfZippable f where
  halfZipWith :: (x -> y -> Maybe z) -> f x -> f y -> Maybe (f z)

instance HalfZippable [] where
  halfZipWith f [] [] = pure []
  halfZipWith f (x : xs) (y : ys) = (:) <$> f x y <*> halfZipWith f xs ys
  halfZipWith _ _ _ = empty

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
  sbst u ss (TM m es) = TM m (sbst u ss es)
  sbst u ss (TC c ts) = TC c (sbst u ss ts)
  sbst u ss (TB t)    = TB (sbst (u + 1) ss t)
  sbst u ss (TE e)    = TE (sbst u ss e)

instance Stan x => Stan (Sub x) where
  stan ms (h :- g) = stan ms h :- stan ms g
  sbst u ss (h :- g) = sbst u ss h :- sbst u ss g


data Rule = (Pat, Pat) :<=: [Sub Tm] deriving Show
data Sub x = [Tm] :- x deriving (Eq, Show, Functor)

data Proof = Tm :<-: Tactic deriving Show
data Tactic
  = Query
  | Derive How [Sub Proof]
  deriving Show
data How
  = Intro Tm
  | Elim Tm
  | Known
  deriving Show
infixl 5 :<-:
infixl 4 :-

pm :: String -> Pat
pm x = PM x mempty

andI :: Rule
andI = (PC "&" [pm "a", pm "b"], PC "AndI" []) :<=:
  [ [] :- TM "a" []
  , [] :- TM "b" []
  ]

orIL :: Rule
orIL = (PC "|" [pm "a", pm "b"], PC "OrIL" []) :<=:
  [ [] :- TM "a" []
  ]

orIR :: Rule
orIR = (PC "|" [pm "a", pm "b"], PC "OrIR" []) :<=:
  [ [] :- TM "b" []
  ]

impI :: Rule
impI = (PC "->" [pm "a", pm "b"], PC "ImpI" []) :<=:
  [ [TM "a" []] :- TM "b" []
  ]

ask :: [Rule] -> [Tm] -> Proof -> Proof
ask rules hs (g :<-: Derive (Intro r) ps) =
  case [ stan (m1 ++ m2) xs
       | (p, q) :<=: xs <- rules
       , m1 <- foldMap pure $ match p g
       , m2 <- foldMap pure $ match q r
       ] of
    [xs] -> g :<-: Derive (Intro r) (asks rules hs xs ps)
    _ -> g :<-: Query
ask rules hs (g :<-: Derive (Elim r) ps) =
  g :<-: Derive (Elim r) (asks rules hs
  (([] :- r) :
  [ s
  | (p, q) :<=: xs <- rules
  , m <- foldMap pure $ match p r
  , s <- case stan m xs of
      [hs :- t] -> map ([] :-) hs ++ [[t] :- g]
      ys -> [map impify ys :- g]
  ]) -- hole what about metas in q?
  ps)
ask rules hs p@(g :<-: Derive Known []) | elem g hs = p
ask rules hs (g :<-: _) = g :<-: Query

impify :: Sub Tm -> Tm
impify ([] :- t) = t
impify ((s : ss) :- t) = TC "->" [s, impify (ss :- t)]

asks :: [Rule] -> [Tm] -> [Sub Tm] -> [Sub Proof] -> [Sub Proof]
asks rules hs xs [] = map (fmap (:<-: Query)) (filter (unknown hs) xs)
asks rules hs xs ((ks :- p@(g :<-: t)) : ps)
  | Just xs <- coFind ((ks :- g) ==) xs
  = (ks :- ask rules (ks ++ hs) p) : asks rules hs xs ps
asks rules hs xs (_ : ps) = asks rules hs xs ps

coFind :: (a -> Bool) -> [a] -> Maybe [a]
coFind p [] = Nothing
coFind p (x : xs)
  | p x = Just xs
  | otherwise = (x :) <$> coFind p xs

unknown :: [Tm] -> Sub Tm -> Bool
unknown hs (ks :- g) = not (elem g (ks ++ hs))

test1 :: Proof
test1 = ask [andI] [] (TC "&" [TE (TV 0), TE (TV 1)] :<-: Derive (Intro (TC "AndI" [])) [])

test2 :: Proof
test2 = ask [andI] [TE (TV 0), TE (TV 1)] (TC "&" [TE (TV 0), TE (TV 1)] :<-: Derive (Intro (TC "AndI" [])) [])

test3 :: Proof
test3 = ask [andI,orIL,orIR,impI] [] $
  TC "->" [TC "&" [a, b], TC "&" [b, a]] :<-: Derive (Intro (TC "ImpI" []))
    [[TC "&" [a, b]] :- TC "&" [b, a] :<-: Derive (Elim (TC "&" [a, b]))
     [[a, b] :- TC "&" [b, a] :<-: Derive (Intro (TC "AndI" []))
       []
     ]
    ]
  where
  a = TE (TV 1)
  b = TE (TV 0)

test4 :: Proof
test4 = ask [andI,orIL,orIR,impI] [] $
  TC "->" [TC "->" [a, b],
    TC "->" [TC "->" [b, c],
      TC "->" [a, c] ] ] :<-: Derive (Intro (TC "ImpI" []))
    [[TC "->" [a, b]] :- TC "->" [TC "->" [b, c],
           TC "->" [a, c] ] :<-: Derive (Intro (TC "ImpI" []))
      [[TC "->" [b, c]] :- TC "->" [a, c] :<-: Derive (Intro (TC "ImpI" []))
      [[a] :- c :<-: Derive (Elim (TC "->" [b, c]))
        [[] :- b :<-: Derive (Elim (TC "->" [a, b]))
          []]]
      ]
    ]
  where
  a = TE (TV 2)
  b = TE (TV 1)
  c = TE (TV 0)
  