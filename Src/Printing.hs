module Ask.Src.Printing where

import qualified Data.Map as M
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

pnom :: Context -> Int -> String
pnom B0 i = "???" ++ show i
pnom (ga :< Var x) 0 = x
pnom (ga :< Var _) i = pnom ga (i - 1)
pnom (ga :< _) i     = pnom ga i

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

ppTmR :: Setup -> Context -> Spot -> TmR -> String
ppTmR setup ga spot t = case readyTmR t of
  Left t -> ppTm setup ga spot t
  Right ls -> rfold lout ls ""

ppTm :: Setup -> Context -> Spot -> Tm -> String
ppTm setup ga spot (TC f@(c : s) as)
  | isAlpha c = go f
  | otherwise = case as of
    [x, y] ->
      let (p, a) = case M.lookup f (fixities setup) of
            Nothing -> (9, LAsso)
            Just x  -> x
      in  pppa spot (Inf (p, a))
            (ppTm setup ga (Infix (p, Left a)) x
             ++ " " ++ f ++ " " ++
             ppTm setup ga (Infix (p, Right a)) y)
    _ -> go ("(" ++ f ++ ")")
 where
  go f = case as of
    [] -> f
    _  -> pppa spot App (f ++ (as >>= ((" " ++) . ppTm setup ga Arg)))
ppTm setup ga spot (TE e) = ppEl setup ga spot e
ppTm _ _ _ t = show t

ppEl :: Setup -> Context -> Spot -> Syn -> String
ppEl setup ga _ (TV i) = pnom ga i
ppEl setup ga spot (t ::: ty) = pppa spot Rad
  (ppTm setup ga RadSpot t ++ " :: " ++ ppTm setup ga RadSpot ty)
ppEl setup ga spot (f :$ s) = pppa spot App
  (ppEl setup ga Fun f ++ " " ++ ppTm setup ga Arg s)

