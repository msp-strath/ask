module Ask.Src.HalfZip where

class HalfZippable f where
  halfZipWith :: (x -> y -> Maybe z) -> f x -> f y -> Maybe (f z)

instance HalfZippable [] where
  halfZipWith f [] [] = Just []
  halfZipWith f (x : xs) (y : ys) = (:) <$> f x y <*> halfZipWith f xs ys
  halfZipWith _ _ _ = Nothing
