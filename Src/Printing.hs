{-# LANGUAGE LambdaCase #-}

module Ask.Src.Printing where

import Data.Char
import Data.List

import Ask.Src.Hide
import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Context

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

pinx :: Int -> AM String
pinx i = return $ "???"

pnom :: Nom -> AM String
pnom x = cope (nomBKind x) (\ gr -> return (show x)) $ \case
  User x -> return x
  _      -> return (show x)

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
  | c == '(' = do
    let n = case span (',' ==) s of
         ([], _) -> 0
         (cs, _) -> 1 + length cs
    if n /= length as then go f else do
      as <- traverse (ppTm AllOK) as
      return $ "(" ++ intercalate ", " as ++ ")"
  | f == "=" = case as of
      [ty, lhs, rhs] -> do
        let (lhs', rhs') = case (lhs, rhs) of
              (TE _, _) -> (lhs, rhs)
              (_, TE _) -> (lhs, rhs)
              _ -> (TE (lhs ::: ty), rhs)
        lhs <- ppTm (Infix (4, Left NAsso)) lhs'
        rhs <- ppTm (Infix (4, Right NAsso)) rhs'
        return $ pppa spot (Inf (4, NAsso)) (lhs ++ " = " ++ rhs)
      _ -> go "(=)"
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
      return $ pppa spot App (f ++ (as >>= (" " ++)))
ppTm spot (TE e) = ppEl spot e
ppTm _ t = return $ show t

ppEl :: Spot -> Syn -> AM String
ppEl _ (TV i) = pinx i
ppEl _ (TP (x, _)) = pnom x
ppEl spot (t ::: ty) = do
  t <- ppTm RadSpot t
  ty <- ppTm RadSpot ty
  return . pppa spot Rad $ t ++ " :: " ++ ty
ppEl spot (f :$ s) = do
  f <- ppEl Fun f
  s <-  ppTm Arg s
  return . pppa spot App $ f ++ " " ++ s
ppEl spot (TF (f, Hide sch) ss ts) = do
  ss <- return $ dump sch ss
  ppTm spot (TC (fst (last f)) (ss ++ ts))
  -- terrible hack
 where
  dump (Al a t) (s : ss) = dump (t // (s ::: a)) ss
  dump _ ss = ss


ppGripe :: Gripe -> AM String
ppGripe Surplus = return "I don't see why you need this"
ppGripe (Duplication ty c) = do
  ty <- ppTm AllOK ty
  return $ "I already have something called " ++ c ++ " that makes things in " ++ ty
ppGripe (Scope x) = return $ "I can't find " ++ x ++ " in scope"
ppGripe (ByBadRule r t) = do
  t <- ppTm AllOK t
  return $ "I can't find a rule called " ++ r ++ " that would prove " ++ t
ppGripe (ByAmbiguous r t) = do
  t <- ppTm AllOK t
  return $ "Please report a bug: I have too many rules called " ++ r ++ " that would prove " ++ t
ppGripe (TestNeedsEq g) = do
  g <- ppTm AllOK g
  return $ "I can only test equations, not " ++ g
ppGripe (FromNeedsConnective (ls, _)) = return $
  rfold lout ls " has no main connective for 'from' to eliminate."
ppGripe (NotGiven p) = do
  p <- ppTm AllOK p
  return $ "I do not remember being given " ++ p
ppGripe (NotARule (ls, _)) = return $ rfold lout ls " is not the right shape to be a rule."
ppGripe Mardiness = return $
  "I seem to be unhappy but I can't articulate why, except that it's Conor's fault."
ppGripe (NotADataType t) = do
  t <- ppTm AllOK t
  return $ t ++ " is not a data type and cannot be split into cases"
ppGripe (WrongNumOfArgs c n as) = return $
  c ++ " expects " ++ count n ++ " but you have given it " ++ blat as
  where
  count 0 = "no arguments"
  count 1 = "one argument"
  count 2 = "two arguments"
  count 3 = "three arguments"
  count n = show n ++ " arguments"
  blat [] = "none"
  blat [(ls, _)] = rfold lout ls ""
  blat ((ls, _) : as) = rfold lout ls $ " and " ++ blat as
ppGripe (DoesNotMake c ty) = do
  ty <- ppTm AllOK ty
  return $ c ++ " cannot make a thing of type " ++ ty
ppGripe (OverOverload c) = return $
  "Please report a bug. " ++ c ++ " has unsafe overloading."
ppGripe (BadFName f) = return $ case f of
  [] -> "Please report a bug. Somehow, the empty string is the name of a thing."
  c : _
    | isUpper c ->
      "You declared " ++ f ++
      " but function names should begin in lowercase. (Did you mean data ... = "
      ++ f ++ " ...?)"
  _ -> "I'm afraid that " ++ f ++ " is an unsuitable name for a function."
    
ppGripe FAIL = return $
  "It went wrong but I've forgotten how. Please ask a human for help."
ppGripe g = return $ show g
