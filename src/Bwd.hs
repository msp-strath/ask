module Bwd where

data Bwd x = B0 | Bwd x :< x

(<>>) :: Bwd x -> [x] -> [x]
B0 <>> ys = ys
(xz :< x) <>> ys = xz <>> (x : ys)
