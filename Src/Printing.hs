module Ask.Src.Printing where

import Data.Char

import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Scoping

data Spot = AllOK | RadSpot | Infix (Int, Either Assocy Assocy) | Fun | Arg deriving (Show, Eq)
data Wot = Rad | Inf (Int, Assocy) | App deriving (Show, Eq)
instance Ord Wot where
  compare Rad Rad = EQ
  compare Rad (Inf _) = LT
  compare Rad App = LT
  compare (Inf _) Rad = GT
  compare (Inf (i, _)) (Inf (j, _)) = compare i j
  compare (Inf _) App = LT
  compare App App = EQ
  compare App _   = GT
  -- x <= y means you can put a y anywhere you can put an x with no parens

pnom :: Int -> AM String
pnom i = AM $ \ _ ga -> Right (go ga i) where
  go B0 i = "???" ++ show i
  go (ga :< Var x) 0 = x
  go (ga :< Var _) i = go ga (i - 1)
  go (ga :< _) i     = go ga i

pppa :: Spot -> Wot -> String -> String
pppa x y s = if paren x y then "(" ++ s ++ ")" else s where
  paren AllOK _ = False
  paren RadSpot w = w <= Rad
  paren (Infix (i, a)) (Inf (j, b)) =
    j < i || (j == i && case (a, b) of
      (Left LAsso, LAsso) -> False
      (Right RAsso, RAsso) -> False
      _ -> True)
  paren (Infix _) App = False
  paren Fun App = False
  paren _ _ = True

readyTmR :: TmR -> Either Tm [LexL]
readyTmR (My t) = Left t
readyTmR (Our _ (ls, _)) = Right ls
readyTmR (Your (ls, _)) = Right ls

ppTmR :: Spot -> TmR -> AM String
ppTmR spot t = case readyTmR t of
  Left t -> ppTm spot t
  Right ls -> return $ rfold lout ls ""

ppTm :: Spot -> Tm -> AM String
ppTm spot (TC f@(c : s) as)
  | isAlpha c = go f
  | otherwise = case as of
    [x, y] -> do
      (p, a) <- fixity f
      x <- ppTm (Infix (p, Left a)) x
      y <- ppTm (Infix (p, Right a)) y
      return $ pppa spot (Inf (p, a)) (x ++ " " ++ f ++ " " ++ y)
    _ -> go ("(" ++ f ++ ")")
 where
  go f = case as of
    [] -> return f
    _  -> do
      as <- traverse (ppTm Arg) as
      return $ f ++ (as >>= (" " ++))
ppTm spot (TE e) = ppEl spot e
ppTm _ t = return $ show t

ppEl :: Spot -> Syn -> AM String
ppEl _ (TV i) = pnom i
ppEl spot (t ::: ty) = do
  t <- ppTm RadSpot t
  ty <- ppTm RadSpot ty
  return . pppa spot Rad $ t ++ " :: " ++ ty
ppEl spot (f :$ s) = do
  f <- ppEl Fun f
  s <-  ppTm Arg s
  return . pppa spot App $ f ++ " " ++ s

