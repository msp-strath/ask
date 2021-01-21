module Ask.Src.Hide where

newtype Hide x = Hide {peek :: x}

instance Show (Hide x) where show _ = ""
instance Eq (Hide x) where _ == _ = True
