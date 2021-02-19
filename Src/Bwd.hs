{-# LANGUAGE DeriveTraversable #-}

module Ask.Src.Bwd where

infixl 3 :<, <><

data Bwd x = B0 | Bwd x :< x deriving (Eq, Ord, Functor, Foldable, Traversable)
instance Show x => Show (Bwd x) where show xz = show (xz <>> [])

(<>>) :: Bwd x -> [x] -> [x]
B0 <>> ys = ys
(xz :< x) <>> ys = xz <>> (x : ys)

(<><) :: Bwd x -> [x] -> Bwd x
xz <>< [] = xz
xz <>< (x : xs) = (xz :< x) <>< xs

instance Monoid (Bwd x) where
  mempty = B0
  mappend xz B0        = xz
  mappend xz (yz :< y) = mappend xz yz :< y

instance Semigroup (Bwd x) where (<>) = mappend

(<?) :: Bwd x -> Int -> Either Int x
(xz :< x) <? 0 = Right x
(xz :< x) <? n = xz <? (n - 1)
B0        <? n = Left n

(<!) :: Bwd x -> Int -> x
xz <! n = case xz <? n of
  Right x -> x
  Left _  -> error "hard fail for bounds error"

nearest :: (x -> Maybe y) -> Bwd x -> Maybe (Bwd x, y, [x])
nearest p xz = go xz [] where
  go B0 _ = Nothing
  go (xz :< x) xs = case p x of
    Just y -> Just (xz, y, xs)
    Nothing -> go xz (x : xs)

wherez :: (x -> Bool) -> Bwd x -> Maybe Int
wherez p = go 0 where
  go _ B0 = Nothing
  go i (xz :< x)
    | p x       = Just i
    | otherwise = go (i + 1) xz
