{-# LANGUAGE DeriveTraversable #-}

module Ask.Src.Bwd where

infixl 3 :<, <><

data Bwd x = B0 | Bwd x :< x deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

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