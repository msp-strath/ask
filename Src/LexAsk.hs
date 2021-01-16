{-# LANGUAGE EmptyDataDeriving, DeriveFunctor #-}

module LexAsk where

import Data.Char
import Data.List

import Bwd

{-
Let's not do full-on Haskell lexing.
-}

lexAll :: String -> [[LexL]]
lexAll = lines2List . lexPhase1 . lexPhase0

data Tok f
  = Lid
  | Key
  | Uid
  | Und
  | Sym
  | Spc
  | Num
  | Str
  | Chr
  | Ret
  | Cmm
  | Bad
  | T (f (Lex f))

type Pos = (Int, Int) -- row and column; origin is 1
type Lex f = (Tok f, Pos, String)
txt :: Lex f -> String
txt (_, _, s) = s

bad :: Lex f -> Lex f
bad (_, p, s) = (Bad, p, s)

class PShow f where
  pshow :: Show x => f x -> String

instance PShow f => Show (Tok f) where
  show Lid = "Lid"
  show Key = "Key"
  show Uid = "Uid"
  show Und = "Und"
  show Sym = "Sym"
  show Spc = "Spc"
  show Num = "Num"
  show Str = "Str"
  show Chr = "Chr"
  show Ret = "Ret"
  show Cmm = "Cmm"
  show Bad = "Bad"
  show (T tf) = pshow tf

class PEq f where
  peq :: Eq x => f x -> f x -> Bool

instance PEq f => Eq (Tok f) where
  Lid == Lid = True
  Key == Key = True
  Uid == Uid = True
  Und == Und = True
  Sym == Sym = True
  Spc == Spc = True
  Num == Num = True
  Str == Str = True
  Chr == Chr = True
  Ret == Ret = True
  Cmm == Cmm = True
  Bad == Bad = True
  T x == T y = peq x y
  _   == _   = False

data K0 x deriving (Show, Eq)
instance PShow K0 where pshow = show
instance PEq K0 where peq = (==)

type Tok0 = Tok K0
type Lex0 = Lex K0

tok0 :: Tok0 -> Tok f
tok0 Lid = Lid
tok0 Key = Key
tok0 Uid = Uid
tok0 Und = Und
tok0 Sym = Sym
tok0 Spc = Spc
tok0 Num = Num
tok0 Str = Str
tok0 Chr = Chr
tok0 Ret = Ret
tok0 Cmm = Cmm
tok0 Bad = Bad

lex0 :: Lex0 -> (Tok f, Pos, String)
lex0 (t, p, s) = (tok0 t, p, s)

lexPhase0 :: String -> [Lex0]
lexPhase0 = phase0 (1, 1) . untab 1

untab :: Int -> String -> String
untab i [] = []
untab i ('\t' : s) = ' ' : skip (i + 1) s where
  skip i s | i `mod` 8 == 1 = untab i s
           | otherwise = ' ' : skip (i + 1) s
untab i (c : s) = c : untab (if c `elem` newlines then 1 else i + 1) s

phase0 :: Pos -> String -> [Lex0]
phase0 _ [] = []
phase0 p@(y, x) ('"' : s) = literal0 Str '"' p (B0 :< '"') (y, x + 1) s
phase0 p@(y, x) ('\'' : s) = literal0 Chr '\'' p (B0 :< '"') (y, x + 1) s
phase0 p@(y, x) ('{' : '-' : s) = brcomm0 p (B0 :< '{' :< '-') 0 (y, x + 2) s
phase0 p@(y, x) ('-' : '-' : s) | commenty s =
  more0 Cmm p (B0 :< '-' :< '-') (y, x + 2) (not . (`elem` newlines)) s
  where
    commenty ('-' : s) = commenty s
    commenty (c : _) | c `elem` symbols = False
    commenty _ = True
phase0 p@(y, x) ('_' : c : cs) | isIdTaily c
  = more0 Lid p (B0 :< '_' :< c)(y, x + 2) isIdTaily cs
phase0 p@(y, x) ('_' : cs) = (Und, p, "_") : phase0 (y, x + 1) cs
phase0 p@(y, x) (c : cs) = case c of
  ' ' -> space0 p p 0 (c : cs)
  _ | c `elem` specials -> (Sym, p, [c]) : phase0 (y, x + 1) cs
    | c `elem` symbols -> more0 Sym p (B0 :< c) (y, x + 1) (`elem` symbols) cs
    | c `elem` newlines -> (Ret, p, [c]) : phase0 (y + 1, 1) cs
    | isDigit c -> more0 Num p (B0 :< c) (y, x + 1) isDigit cs
    | isLower c -> more0 Lid p (B0 :< c) (y, x + 1) isIdTaily cs
    | isUpper c -> more0 Uid p (B0 :< c) (y, x + 1) isIdTaily cs

more0 :: Tok0 -> Pos -> Bwd Char -> Pos -> (Char -> Bool) -> String -> [Lex0]
more0 t o cz (y, x) f (c : cs) | f c = more0 t o (cz :< c) (y, x + 1) f cs
more0 t o cz p f s = (if b then Key else t, o, w) : phase0 p s where
  w = cz <>> ""
  b = t == Lid && (w `elem` keywords)

literal0 :: Tok0 -> Char -> Pos -> Bwd Char -> Pos -> String -> [Lex0]
literal0 t e o cz (y, x) (c : s) | c == e = (t, o, cz <>> [c]) : phase0 (y, x + 1) s
literal0 t e o cz (y, x) ('\\' : c : s)
  | c > ' ' = literal0 t e o (cz :< '\\' :< c) (y, x + 2) s
  | otherwise = multilit0 t e o (cz :< '\\') (y, x + 1) (c : s)
literal0 t e o cz (y, x) (c : s) = literal0 t e o (cz :< c) (y, x + 1) s
literal0 t e o cz _ [] = [(Bad, o, cz <>> "")]

multilit0 :: Tok0 -> Char -> Pos -> Bwd Char -> Pos -> String -> [Lex0]
multilit0 t e o cz (y, x) ('\\' : cs) = literal0 t e o (cz :< '\\') (y, x + 1) cs
multilit0 t e o cz (y, x) (' ' : cs) = multilit0 t e o (cz :< ' ') (y, x + 1) cs
multilit0 t e o cz (y, x) (c : cs) | c `elem` newlines = multilit0 t e o (cz :< c) (y + 1, 1) cs
multilit0 t e o cz p s = (Bad, o, cz <>> s) : phase0 p s

brcomm0 :: Pos -> Bwd Char -> Int -> Pos -> String -> [Lex0]
brcomm0 o cz n (y, x) ('-' : '}' : s) = case n of
  0 -> (Cmm, o, cz <>> "-}") : phase0 (y, x + 2) s
  n -> brcomm0 o (cz :< '-' :< '}') (n - 1) (y, x + 2) s
brcomm0 o cz n (y, x) ('{' : '-' : s) =
  brcomm0 o (cz :< '{' :< '-') (n + 1) (y, x + 2) s
brcomm0 o cz n (y, x) (c : s) =
  brcomm0 o (cz :< c) n (if c `elem` newlines then (y + 1, 1) else (y, x + 1)) s
brcomm0 o cz n _ [] = [(Bad, o, cz <>> "")]

space0 :: Pos -> Pos -> Int -> String -> [Lex0]
space0 o _ i [] = []
space0 o p@(y, x) i s@(c : cs) = case c of
  ' ' -> space0 o (y, x + 1) (i + 1) cs
  _ -> (Spc, o, replicate i ' ') : phase0 p s

newlines :: String
newlines = "\r\n"

specials :: String
specials = "(),;[]`{}"

symbols :: String
symbols = "!#$%&*+./<=>?@\\^|-~:"

keywords :: [String]
keywords =
  [ "case", "class", "instance", "data", "do", "if", "then", "else", "where", "let", "in", "of"
  , "module", "import", "deriving", "infix", "infixl", "infixr"
  , "prop", "prove", "by", "from", "contrarily", "given"
  ]

isIdTaily :: Char -> Bool
isIdTaily c = isAlphaNum c || c `elem` "'_"

data Lay l
  = (Pos, String, [l]) :-! Maybe (l, Lines l, l)
  | LB l [l] l
  deriving (Functor, Show, Eq)

instance PEq Lay where peq = (==)
instance PShow Lay where pshow = show

data Lines l = [l] :-& More l deriving (Functor, Show, Eq)
data More l = Stop | l :-/ Lines l deriving (Functor, Show, Eq)
infixr 5 :-&
infixr 5 :-/

type TokL = Tok Lay
type LexL = Lex Lay

type Layer = (Int, Bwd [LexL], Bwd LexL)

heralds :: [String]
heralds = ["where", "do", "of", "let"]

layEnders :: [(String, String)]
layEnders = [("do", "where"), ("of","where"), ("let", "in")]

gappy :: Lex f -> Bool
gappy (t, _, _) = case t of
  Spc -> True
  Ret -> True
  Cmm -> True
  _   -> False

pfirst :: [Lex0] -> Pos
pfirst ((_, p, s) : _) = p
pfirst [] = (maxBound, maxBound)

munch :: Bool -> (String, Int) -> [Lex0] -> ([LexL], [LexL], [Lex0])
munch b (k, i) ls = case span gappy ls of
  (ss, []) -> ([], map lex0 ss, [])
  (ss, l@(t, p@(y, x), s) : ls)
    | t == Sym && s == ";" || x <= i && b
    -> ([], map lex0 ss, l : ls)
    | t == Sym && s == "}" && i == 0
    -> ([], map lex0 ss, l : ls)
    | t == Sym && s == "{"
    -> let (bl, c, us) = laylines ("", 0) ls
           (ts, ss', vs) = munch True (k, i) us
       in ( map lex0 ss ++
            (T ((p, "", []) :-! Just (lex0 l, bl, c)), p, "") : ts
          , ss'
          , vs)
    | t == Key && (k, s) `elem` layEnders
    -> ([], map lex0 ss, l : ls)
    | t == Key && s `elem` heralds
    -> let (ps, mls, us) = munches (s, i) ls
           (ts, ss', vs) = munch True (k, i) us
       in (map lex0 ss ++ (T ((p, s, ps) :-! mls), p, "") : ts, ss', vs)
    | otherwise
    -> let (ts, ss', us) = munch True (k, i) ls
       in  (map lex0 ss ++ lex0 l : ts, ss', us)

munches :: (String, Int) -> [Lex0] -> ([LexL], Maybe (LexL, Lines LexL, LexL), [Lex0])
munches (k, i) ls = case span gappy ls of
  (ss, l@(t, p@(y, x), s) : ls)
    | t == Sym && s == "{"
    -> let (xs, c, us) = laylines (k, 0) ls in
       (map lex0 ss, Just (lex0 l, xs, c), us)
    | x > i
    -> let (xs, c, us) = laylines (k, x) (l : ls) in
       (map lex0 ss, Just ((Spc, p, ""), xs, c), us)
  (ss, ls) -> (map lex0 ss, Nothing, ls)

laylines :: (String, Int) -> [Lex0] -> (Lines LexL, LexL, [Lex0])
laylines (k, i) ls = case munch False (k, i) ls of
  (ts, ss, l@(t, p@(y, x), s) : ls)
    | t == Sym && s == ";" && x >= i
    -> let (xs, c, us) = laylines (k, i) ls in
       ((brackety B0 B0 ts ++ ss) :-& lex0 l :-/ xs, c, us)
    | x == i
    -> let (xs, c, us) = laylines (k, i) (l : ls) in
       ((brackety B0 B0 ts ++ ss) :-& (Spc, p, "") :-/ xs, c, us)
    | t == Sym && s == "}" && i == 0
    -> ((brackety B0 B0 ts ++ ss) :-& Stop, lex0 l, ls)
  (ts, ss, ls)
    -> ((brackety B0 B0 ts ++ ss) :-& Stop, (Spc, pfirst ls, ""), ls)

brackety :: Bwd (Bwd LexL, LexL) -> Bwd LexL -> [LexL] -> [LexL]
brackety bz lz [] = dump bz (lz <>> []) where
  dump B0 ls = ls
  dump (bz :< (kz, k)) ls = dump bz (kz <>> (bad k : ls))
brackety bz lz (l@(Sym, _, [o]) : ls) | o `elem` "([{" =
  brackety (bz :< (lz, l)) B0 ls
brackety bz lz (l@(Sym, _, [c]) : ls) | c `elem` ")]}" =
  blat bz lz where
  blat B0 lz = brackety B0 (lz :< bad l) ls
  blat (bz :< (kz, k@(_, p, [o]))) lz
    | brackMatch o c
    = brackety bz (kz :< (T (LB k (lz <>> []) l), p, "")) ls
    | otherwise -- bad
    = blat bz ((kz :< bad k) <> lz)
brackety bz lz (l : ls) = brackety bz (lz :< l) ls

brackMatch :: Char -> Char -> Bool
brackMatch '(' ')' = True
brackMatch '[' ']' = True
brackMatch '{' '}' = True
brackMatch _   _   = False

lines2List :: Lines LexL -> [[LexL]]
lines2List (l :-& m) = l : case m of
  Stop -> []
  _ :-/ ls -> lines2List ls

lexPhase1 :: [Lex0] -> Lines LexL
lexPhase1 ts = ls where (ls, _, _) = laylines ("", 1) ts

rfold :: (x -> t -> t) -> [x] -> t -> t
rfold t2t xs t = foldr t2t t xs

lout :: LexL -> String -> String
lout (T ((_, x, lp) :-! m), _ , _) = (x ++) . rfold lout lp . case m of
  Nothing -> id
  Just (lo, lls, lc) -> lout lo . go lls . lout lc
 where
  go (ls :-& m) = rfold lout ls . case m of
    Stop -> id
    lm :-/ lls -> lout lm . go lls
lout (T (LB lo ls lc), _, _) = lout lo . rfold lout ls . lout lc
lout (_, _, s) = (s ++)

data WhereKind
  = Dental Int
  | Bracy [LexL] [LexL] [LexL]
  deriving Show

whereKind :: Int -> Maybe (LexL, Lines LexL, LexL) -> WhereKind
whereKind p Nothing = Dental (p + 2)
whereKind p (Just (o, ls, c)) = case o of
  (Sym, _, o) -> bracy ls
  _ -> Dental (dental ls)
 where
  bracy (l :-& m) = case span gappy l of
    (pre, mo) -> chasy pre (mo :-& m)
  chasy pre (ls :-& s :-/ ms :-& Stop) = Bracy pre (se ++ s : mi) post where
    (_, se) = naps gappy ls
    (mi, _) = span gappy ms
    (_, post) = naps gappy ms
  chasy pre (_ :-& _ :-/ r) = chasy pre r
  chasy pre (_ :-& Stop) = Bracy
    pre
    [(Sym,(0,0),";"), (Ret,(0,0),"\n"), (Spc,(0,0),replicate (p + 2) ' ')]
    []
  naps p xs = (reverse zs, reverse ys) where (ys, zs) = span p (reverse xs)
  dental (l :-& m) = case span gappy l of
    (_, (_, (_, d), _) : _) -> d - 1
    _ -> case m of
      Stop -> p + 2
      _ :-/ ls -> dental ls