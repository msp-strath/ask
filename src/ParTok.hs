{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , PatternGuards
  , LambdaCase
#-}

module ParTok where

import Control.Monad
import Control.Applicative
import Data.List

import Debug.Trace

import Bwd
import LexAsk

newtype ParTok x = ParTok {parTok
  :: [LexL]
  -> [([LexL], x, [LexL])]
  } deriving (Semigroup, Monoid)

instance Monad ParTok where
  return x = ParTok $ \ ls -> [([], x, ls)]
  ParTok ps >>= k = ParTok $ \ ls -> do
    (ks, s, ls) <- ps ls
    (kt, t, ls) <- parTok (k s) ls
    return (ks ++ kt, t, ls)

instance Applicative ParTok where
  pure = return
  (<*>) = ap

instance Functor ParTok where
  fmap = ap . return

instance Alternative ParTok where
  empty = mempty
  (<|>) = (<>)

(?>) :: ParTok x -> ParTok x -> ParTok x
(?>) (ParTok f) (ParTok g) = ParTok $ \ ls -> case f ls of
  [] -> g ls
  xs -> xs

eat :: (LexL -> Maybe x) -> ParTok x
eat f = ParTok $ \case
  l : ls | Just x <- f l -> return ([l], x, ls)
  _ -> []

the :: Tok Lay -> String -> ParTok ()
the t s = eat $ \ (u, _, r) -> guard $ u == t && r == s

kinda :: Tok Lay -> ParTok LexL
kinda t = eat $ \ l@(u, _, _) -> do guard $ u == t ; return l

brk :: Char -> ParTok x -> ParTok x
brk c p = ParTok $ \case
  (l@(T (LB (Sym, _, [o]) ks _), _, _) : ls) | c == o ->
    [([l], x, ls) | (_, x, []) <- parTok p ks]
  _ -> []

spc :: ParTok ()
spc = ParTok $ \ ls -> let (ks, ms) = span gappy ls in [(ks, (), ms)]

spd :: ParTok x -> ParTok x
spd p = id <$ spc <*> p <* spc

sep :: ParTok x -> ParTok () -> ParTok [x]
sep p s = (:) <$> spd p <*> many (id <$ s <*> spd p)
      <|> [] <$ spc

eol :: ParTok ()
eol = ParTok $ \case
  [] -> [([], (), [])]
  _ -> []

lol :: String -> ParTok x -> ParTok [x]
lol k p = ParTok $ \case
  l@(T ((_, h, _) :-! m) , _, _) : ls | h == k -> case m of
    Nothing -> [([l], [], ls)]
    Just (_, pl, _) -> grok pl >>= \ x -> [([l], x, ls)]
  _ -> []
  where
  grok (ks :-& m)
    | all gappy ks = glom m
    | otherwise = do
    (_, x, []) <- parTok p ks
    (x :) <$> glom m
  glom Stop = return []
  glom (_ :-/ m) = grok m

ext :: ParTok x -> ParTok ([LexL], x)
ext p = ParTok $ \ ls -> do
  (ks, x, us) <- parTok p ls
  return (ks, (ks, x), us)
