module Ask.Src.Glueing where

import Ask.Src.Tm
import Ask.Src.RawAsk

data TmR
  = My Tm
  | Our Tm Appl
  | Your Appl

instance Show TmR where
  show (My t) = show t
  show (Our t _) = show t
  show (Your (_, a)) = show a

my :: TmR -> Maybe Tm
my (My t) = Just t
my (Our t _) = Just t
my _ = Nothing
