{-# LANGUAGE PatternSynonyms, TupleSections, LambdaCase #-}

module Ask.Src.Bis where

import Control.Monad

import Ask.Src.Bwd

data Chk
  = TC String [Chk]
  | TB (Bind Chk)
  | TE Syn
  deriving Show

data Bind t
  = K t
  | L t
  deriving Show

data Syn
  = TV Int
  | TP Decl
  | Chk ::: Chk
  | Syn :$ Chk
  deriving Show

data Decl = Decl
  { nom :: Integer
  , typ :: Chk
  , wot :: Colour
  , who :: Maybe String
  } deriving Show

data Colour
  = Purple
  | Orange
  | Green Syn
  deriving Show

newtype Mo x = Mo {mo :: State -> Either String (x, State)}

data State = State
  { nonce :: Integer
  , canon :: [((String, String), Chk)]
  } deriving Show

decl :: Chk -> Colour -> Maybe String -> Mo Decl
decl ty co mu = Mo $ \ s -> let x = nonce s in Right
  (Decl x ty co mu, s {nonce = x + 1})

gripe :: String -> Mo x
gripe e = Mo $ \ _ -> Left e

con :: (String, String) -> Mo Chk
con dc = Mo $ \ s -> case lookup dc (canon s) of
  Nothing -> Left $ snd dc ++ " ne fait pas " ++ fst dc
  Just tel -> Right (tel, s)

instance Monad Mo where
  return x = Mo $ \ s -> Right (x, s)
  Mo f >>= k = Mo $ \ s -> case f s of
    Left e -> Left e
    Right (x, s) -> case k x of
      Mo g -> g s
instance Applicative Mo where
  pure = return
  (<*>) = ap
instance Functor Mo where
  fmap = ap . return

data Appl = Head :- [Appl] deriving Show
data Head = UC String | UV String deriving Show

class Sbst t where
  sbst :: Bwd Syn -> Int -> t -> t

instance Sbst Syn where
  sbst ez u e@(TV i)
    | j < 0     = e
    | otherwise = ez <! j
    where j = i - u
  sbst _ _ e@(TP _) = e
  sbst ez u (tm ::: ty) = sbst ez u tm ::: sbst ez u ty
  sbst ez u (tg :$ el)  = sbst ez u tg :$ sbst ez u el

instance Sbst Chk where
  sbst ez u (TC c ts)   = TC c (sbst ez u ts)
  sbst ez u (TB b)      = TB (sbst ez u b)
  sbst ez u (TE e)      = TE (sbst ez u e)

instance Sbst t => Sbst (Bind t) where
  sbst ez u (K t) = K (sbst ez u t)
  sbst ez u (L t) = L (sbst ez (u + 1) t)

instance Sbst t => Sbst [t] where
  sbst ez u = map (sbst ez u)

(//) :: Sbst t => Bind t -> Syn -> t
K t // e = t
L t // e = sbst (B0 :< e) 0 t

pattern V i = TE (TV i)

pattern Type = TC "Type" []
pattern Prop = TC "Prop" []
pattern Size = TC "'Size" []
pattern Ex s b = TC "'Ex" [s, TB b]
pattern Sg s b = TC "'Sg" [s, TB b]
pattern Pr p t = TC "'Pr" [p, t]
pattern Re x   = TC "'Re" [x]
pattern Ok     = TC "'Ok" []
pattern (:->) s t = TC "->" [s, t]
pattern Top = TC "'T" []
pattern Wee x = TC "'<" [x]

runtel :: Bwd (Chk, Chk)
       -> Chk
       -> [Chk]
       -> Mo ( [(Chk, Chk)]
             , Chk
             )
runtel rz (Ex s b) (x : xs) = runtel (rz :< (s, x)) (b // (x ::: s)) xs
runtel rz (Sg s b) (x : xs) = runtel (rz :< (s, x)) (b // (x ::: s)) xs
runtel rz (Pr p t) xs       = runtel rz t xs
runtel rz (Re r)   []       = return (rz <>> [], r)
runtel rz (TE ((TC c ts ::: TC d ss) :$ TC c' [k])) xs | c == c' = do
  (_, t) <- runtel B0 k ts
  runtel rz t xs

isData :: String  -- must be a type constructor
       -> Mo Bool
isData d = con ("Type", d) >>= \case
  Re (Ex Size _) -> return True
  _ -> return False

contel :: String -> [Chk] -> String -> Mo Chk
contel d ss c = do
  tel <- con (d, c)
  (_, tel) <- runtel B0 tel ss
  return tel

myCanon :: [((String, String), Chk)]
myCanon =
  [ ( ("Type", "Type"), Re . Re $ Ok )
  , ( ("Type", "Prop"), Re . Re $ Ok )
  , ( ("Type", "->")
    , Re
    . Sg Type . K . Sg Type . K . Re $ Ok
    )
  , ( ("Type", "(,)")
    , Re
    . Sg Type . K . Sg Type . K . Re $ Ok
    )
  , ( ("(,)", "(,)")
    , Sg Type . L . Sg Type . L . Re
    . Sg (V 1) . K . Sg (V 0) . K . Re $ Ok
    )
  , ( ("Type", "()"), Re . Re $ Ok )
  , ( ("()", "()"), Re . Re $ Ok )
  , ( ("Type", "Nat"), Re . Ex Size . K . Re $ Ok )
  , ( ("Nat", "Z"), Ex Size . K . Re . Re $ Ok )
  , ( ("Nat", "S"), Ex Size . L . Re . Sg (TC "Nat" [Wee (V 0)]) . K . Re $ Ok )
  ]

myState :: State
myState = State
  { nonce = 0
  , canon = myCanon
  }

chkHnf :: (Chk, Chk) -> Mo Chk
chkHnf (trg, TE e) = do
  (e, src) <- hnfSyn e
  ship e src trg
chkHnf (Size, Wee s) = chkHnf (Size, s) >>= \ s -> case s of
  TC _ _  -> return s
  _       -> return $ Wee s
chkHnf (_, t) = return t

hnfSyn :: Syn -> Mo (Syn, Chk)
hnfSyn (TV _) = gripe "de Bruijn"
hnfSyn e@(TP d) = case wot d of
  Green e  -> hnfSyn e
  _        -> return (e, typ d)
hnfSyn (tm ::: ty) = do
  ty <- chkHnf (Type, ty)
  tm <- chkHnf (ty, tm)
  return (tm ::: ty, ty)
hnfSyn (e :$ s) = do
  (e, ty) <- hnfSyn e
  case ty of
    TC "->" [dom, ran] -> case e of
      TB b ::: _ -> hnfSyn $ (b // (s ::: dom)) ::: ran
      _ -> return (e :$ s, ran)
    _ -> gripe "don't know how to do that"

ship :: Syn -> Chk -> Chk -> Mo Chk
ship e src trg = subtype src trg >>= \case
  True -> case e of
    t ::: _ -> return t
    _ -> return $ TE e
  False -> case (e, src, trg) of
    (e, s :-> t, s' :-> t') -> return . TB . L . TE $
      TE (e :$ TE (V 0 ::: s)) ::: t'
    (TC c ts ::: _, TC d ss, TC d' ss') | d == d' -> do
      tel  <- contel d ss  c
      tel' <- contel d ss' c
      TC c <$> ships ts tel tel'
    _ -> return (TE (TE e ::: trg))

ships :: [Chk] -> Chk -> Chk -> Mo [Chk]
ships [] _ _ = return []
ships (t : ts) (Ex s b) (Ex s' b') = do
  let e = t ::: s
  t' <- ship e s s'
  ts' <- ships ts (b // e) (b' // (t' ::: s'))
  return (t' : ts')
ships (t : ts) (Sg s b) (Sg s' b') = do
  let e = t ::: s
  t' <- ship e s s'
  ts' <- ships ts (b // e) (b' // (t' ::: s'))
  return (t' : ts')
ships ts (Pr _ t) (Pr _ t') = ships ts t t'
ships _ _ _ = gripe "ships in the shite"

subtype :: Chk -> Chk -> Mo Bool
subtype x y = do
  x <- chkHnf (Type, x)
  y <- chkHnf (Type, y)
  case (x, y) of
    (s :-> t, s' :-> t') -> (&&) <$> subtype s' s <*> subtype t t'
    (TC d (i : ss), TC e (j : ts)) | d == e -> isData d >>= \case
      True -> sizle i j >>= \case
        False -> return False
        True  -> equal Type (TC d (j : ss), TC d (j : ts))
      False -> equal Type (x, y)
    _ -> equal Type (x, y)

sizle :: Chk -> Chk -> Mo Bool
sizle i j = chkHnf (Size, j) >>= \case
  Top -> return True
  j -> chkHnf (Size, i) >>= \ i -> case (i, j) of
    (Wee i, Wee j) -> equal Size (i, j)
    (Wee i, j)     -> equal Size (i, j)
    _              -> return False

equal :: Chk -> (Chk, Chk) -> Mo Bool
equal ty (a, b) = do
  ty <- chkHnf (Type, ty)
  a <- chkHnf (ty, a)
  b <- chkHnf (ty, b)
  case ty of
    s :-> t -> do
      xd <- decl s Purple Nothing
      equal t (TE ((a ::: ty) :$ TE (TP xd)), TE ((b ::: ty) :$ TE (TP xd)))
    TC d ss -> case (a, b) of
      (TC c ts, TC c' ts') | c == c' -> do
        tel <- contel d ss c
        eqTel tel ts ts'
      _ -> return False
    _ -> case (a, b) of
      (TE e, TE e') -> eqSyn e e' >>= \case
        Just _ -> return True
        _      -> return False
      _ -> return False

eqTel :: Chk -> [Chk] -> [Chk] -> Mo Bool
eqTel _ [] [] = return True
eqTel (Ex s b) (u : us) (v : vs) = (&&)
  <$> equal s (u, v)
  <*> eqTel (b // (u ::: s)) us vs
eqTel (Sg s b) (u : us) (v : vs) = (&&)
  <$> equal s (u, v)
  <*> eqTel (b // (u ::: s)) us vs
eqTel (Pr p t) us vs = eqTel t us vs
eqTel _ _ _ = return False

eqSyn :: Syn -> Syn -> Mo (Maybe Chk)
eqSyn (TP x) (TP y) | nom x == nom y = return (Just (typ x))
eqSyn (e :$ s) (f :$ t) = eqSyn e f >>= \case
  Just (a :-> b) -> equal a (s, t) >>= \case
    True -> return (Just t)
    False -> return Nothing
  _ -> return Nothing
eqSyn (a ::: s) (b ::: t) = equal Type (s, t) >>= \case
  False -> return Nothing
  True -> equal s (a, b) >>= \case
    True -> return (Just s)
    False -> return Nothing
eqSyn _ _ = return Nothing
