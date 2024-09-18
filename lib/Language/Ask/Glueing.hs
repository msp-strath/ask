module Language.Ask.Glueing where

import Language.Ask.Tm
import Language.Ask.RawAsk

data TmR
  = My Tm
  | Our Tm Appl
  | Your Appl

instance Show TmR where
  show (My t) = show t
  show (Our t _) = show t
  show (Your (_, a)) = show a

instance Stan TmR where
  stan m (My t) = My (stan m t)
  stan m (Our t a) = Our (stan m t) a
  stan m x = x
  sbst u es (My t) = My (sbst u es t)
  sbst u es (Our t a) = Our (sbst u es t) a
  sbst u es x = x
  abst x i (My t) = My <$> abst x i t
  abst x i (Our t a) = Our <$> abst x i t <*> pure a
  abst _ _ x = pure x

my :: TmR -> Maybe Tm
my (My t) = Just t
my (Our t _) = Just t
my _ = Nothing
