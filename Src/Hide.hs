module Ask.Src.Hide where

newtype Hide x = Hide {peek :: x}

instance Show x => Show (Hide x) where show (Hide x) = show x
instance Eq (Hide x) where _ == _ = True
