module Language.Ask.Hide where

newtype Hide x = Hide {peek :: x}

--instance Show x => Show (Hide x) where show (Hide x) = show x
instance Show (Hide x) where show _ = ""
instance Eq (Hide x) where _ == _ = True
