{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , PatternGuards
  , LambdaCase
#-}

module Language.Ask.Parsing where

import Control.Monad
import Control.Applicative
import Data.List

import Language.Ask.OddEven
import Language.Ask.Lexing

newtype ParTok e x = ParTok {parTok
  :: e       -- some sort of read-only environment, never mind what
  -> [LexL]
  -> [([LexL], x, [LexL])]
  } deriving (Semigroup, Monoid)

instance Monad (ParTok e) where
  return x = ParTok $ \ _ ls -> [([], x, ls)]
  ParTok ps >>= k = ParTok $ \ e ls -> do
    (ks, s, ls) <- ps e ls
    (kt, t, ls) <- parTok (k s) e ls
    return (ks ++ kt, t, ls)

instance Applicative (ParTok e) where
  pure = return
  (<*>) = ap

instance Functor (ParTok e) where
  fmap = ap . return

instance Alternative (ParTok e) where
  empty = mempty
  (<|>) = (<>)

(?>) :: ParTok e x -> ParTok e x -> ParTok e x
(?>) (ParTok f) (ParTok g) = ParTok $ \ e ls -> case f e ls of
  [] -> g e ls
  xs -> xs

eat :: (LexL -> Maybe x) -> ParTok e x
eat f = ParTok $ \ e ls -> case ls of
  l : ls | Just x <- f l -> return ([l], x, ls)
  _ -> []

penv :: ParTok e e
penv = ParTok $ \ e ls -> [([], e, ls)]

the :: Tok Lay -> String -> ParTok e ()
the t s = eat $ \ (u, _, r) -> guard $ u == t && r == s

kinda :: Tok Lay -> ParTok e LexL
kinda t = eat $ \ l@(u, _, _) -> do guard $ u == t ; return l

brk :: Char -> ParTok e x -> ParTok e x
brk c p = ParTok $ \ e ls -> case ls of
  (l@(T (LB (Sym, _, [o]) ks _), _, _) : ls) | c == o ->
    [([l], x, ls) | (_, x, []) <- parTok p e ks]
  _ -> []

spc :: ParTok e ()
spc = ParTok $ \ _ ls -> let (ks, ms) = span gappy ls in [(ks, (), ms)]

spd :: ParTok e x -> ParTok e x
spd p = id <$ spc <*> p <* spc

sep :: ParTok e x -> ParTok e () -> ParTok e [x]
sep p s = (:) <$> p <*> many (id <$ s <*> p)
      <|> pure []

eol :: ParTok e ()
eol = ParTok $ \ _ ls -> case ls of
  [] -> [([], (), [])]
  _ -> []

lol :: String -> ParTok e x -> ParTok e (Bloc x)
lol k p = ParTok $ \ en ls -> case ls of
  l@(T ((h, _) :-! o) , _, _) : ls | h == k ->
    grok en o >>= \ x -> [([l], x, ls)]
  _ -> []
  where
  grok en (ss :-/ e) = (ss :-/) <$> grek en e
  grek en Stop = pure Stop
  grek en (ls :-\ o) = (:-\) <$> pa en ls <*> grok en o
  pa en ls = [x | (_, x, []) <- parTok (p <* eol) en ls]

ext :: ParTok e x -> ParTok e ([LexL], x)
ext p = ParTok $ \ e ls -> do
  (ks, x, us) <- parTok p e ls
  return (ks, (ks, x), us)
