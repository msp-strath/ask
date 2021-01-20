module Ask.Src.OddEven where

import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Traversable

data Odd a b = a :-/ Even b a deriving (Show, Eq)
data Even b a = Stop | b :-\ Odd a b deriving (Show, Eq)
infixr 6 :-/
infixr 6 :-\

instance Bitraversable Odd where
  bitraverse f g (a :-/ e) = (:-/) <$> f a <*> bitraverse g f e
instance Bitraversable Even where
  bitraverse _ _ Stop = pure Stop
  bitraverse g f (b :-\ o) = (:-\) <$> g b <*> bitraverse f g o

instance Bifunctor Odd  where bimap = bimapDefault
instance Bifunctor Even where bimap = bimapDefault

instance Bifoldable Odd  where bifoldMap = bifoldMapDefault
instance Bifoldable Even where bifoldMap = bifoldMapDefault

instance Traversable (Odd a)  where traverse = bitraverse pure
instance Traversable (Even b) where traverse = bitraverse pure

instance Functor (Odd a)  where fmap = fmapDefault
instance Functor (Even b) where fmap = fmapDefault

instance Foldable (Odd a)  where foldMap = foldMapDefault
instance Foldable (Even b) where foldMap = foldMapDefault

instance Monoid (Even b a) where
  mempty = Stop
  mappend (b :-\ a :-/ bae) bae' = b :-\ a :-/ mappend bae bae'
instance Semigroup  (Even b a) where (<>) = mappend

infixr 6 `ocato`, `ecato`, `ocate`

ocate :: Odd a b -> Even b a -> Odd a b
ocate (a :-/ bae) bae' = a :-/ bae <> bae'

ecato :: Even a b -> Odd a b -> Odd a b
ecato Stop abo = abo
ecato (a :-\ bao) abo = a :-/ bao `ocato` abo

ocato :: Odd b a -> Odd a b -> Even b a
ocato (b :-/ abe) abo = b :-\ abe `ecato` abo
