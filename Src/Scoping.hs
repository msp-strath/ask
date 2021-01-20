module Ask.Src.Scoping where

import Data.List

import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing


data Setup = Setup
  { introRules :: [Rule]
  , weirdRules :: [Rule]
  , fixities   :: FixityTable
  } deriving Show

byRules :: Setup -> [Rule]
byRules s = introRules s ++ weirdRules s

data Rule =
  (Pat, Pat) :<=
  [ Tm
  ]
  deriving Show

type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String  -- dear god no, fix this to be locally nameless
  deriving (Show, Eq)

applScoTm :: Appl -> (Context, TmR)
applScoTm a@(_, x) = (ga, Our t a) where
  (xs, t) = go x
  ga = B0 <>< map Var (nub xs)
  ge x (ga :< Var y) = if x == y then 0 else 1 + ge x ga
  ge x (ga :< _)     = ge x ga
  go ((t, _, y) :$$ ras) = case t of
      Lid -> (y : ys, TE (foldl (:$) (TV (ge y ga)) ts))
      _   -> (ys, TC y ts)
    where
    (ys, ts) = traverse (go . snd) ras

scoApplTm :: Context -> Appl -> Either String TmR
scoApplTm ga a@(_, t) = ((`Our` a)) <$> go t
  where
    go ((t, _, y) :$$ ras) = case t of
      Lid -> TE <$> ((foldl (:$) . TV) <$> ge y ga <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras
    ge x (ga :< Var y) = if x == y then pure 0 else (1 +) <$> ge x ga
    ge x (ga :< _)     = ge x ga
    ge x B0            = Left x
