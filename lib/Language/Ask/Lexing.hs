{-# LANGUAGE EmptyDataDeriving, DeriveFunctor #-}

module Language.Ask.Lexing where

import Data.Char
import Data.List
import Data.Bifunctor

import Language.Ask.Bwd
import Language.Ask.OddEven

lexAll :: String -> Bloc Line
lexAll = lexPhase1 . lexPhase0

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
    | otherwise -> phase0 (y, x + 1) cs

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
  , "prop", "prove", "proven", "by", "from", "given", "inductively", "define", "defined"
  , "test", "tested", "under"
  ]

isIdTaily :: Char -> Bool
isIdTaily c = isAlphaNum c || c `elem` "'_"

data LayKind = Empty | Denty Int | Bracy deriving (Show, Eq)

data Lay l
  = (String, LayKind) :-! Odd [l] [l]
                    -- gappy/bracy -^   ^- begins and ends non-gappy
  | LB l [l] l
  deriving (Show, Eq)

infixr 5 :-!

-- an EmptyL layout should have [] :-/ Stop as its body
-- a Dental i layout should be indented at column i (> 0), so
--   all but the last odd entry should either be gappy or contain a semicolon
--   its last odd entry should be empty
--   its even entries should start at column i unless preceded by a ; in
--     which case they may be further right
--   (and all non gappies must be >= i)
-- a Bracy layout will have odd entries
--   starting with gap { gap
--   gap ; gap in the middle
--   gap } at the end

instance PEq Lay where peq = (==)
instance PShow Lay where pshow = show

type TokL = Tok Lay
type LexL = Lex Lay
type Line = [LexL] -- signal
type Bloc = Odd [LexL] -- noise


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

data Gimmode
  = Indenting String Int
  | Bracing
  deriving Show

gimme
  :: Gimmode   -- where are we at?
  -> Bool      -- have we found a starting token?
  -> [Lex0]    -- ordinary tokens
  -> ( [LexL]  -- lead space
     , [LexL]  -- chunk begins and ends non-gappy or is empty
     , [Lex0]  -- trailing space
     , [Lex0]  -- unconsumed
     ) -- if chunk empty then lead space must be empty
gimme g b ls = case span gappy ls of
  (ss, []) -> ([], [], ss, [])
  (ss, l@(t, p@(y, x), s) : ls)
    | notMine g b l -> ([], [], ss, l : ls)
    | t == Key && s `elem` heralds -> case layout g s ls of
      (l, ls) -> case gimme g True ls of
        (sl, ch, st, ls) -> (map lex0 ss, (T l, p, "") : sl ++ ch, st, ls)
  (ss, l : ls) -> case gimme g True ls of
    (sl, ch, st, ls) ->
      ( map lex0 ss
      , (if b then id else brackety) (lex0 l : sl ++ ch)
      , st
      , ls)

notMine :: Gimmode -> Bool -> Lex0 -> Bool
notMine Bracing _ (t, p@(y, x), s) = elem (t, s) [(Sym, ";"), (Sym, "}")]
notMine (Indenting h i) started (t, p@(y, x), s) =
  x < i || (started && x == i) || elem (h, s) layEnders


layout
  :: Gimmode     -- what's our enclosing context?
  -> String      -- the layout herald
  -> [Lex0]      -- the tokens after the herald
  -> ( Lay LexL  -- the lump of layout
     , [Lex0]    -- the unconsumed input
     )
layout g h ls = case span gappy ls of
  (ss, []) -> ((h, Empty) :-! [] :-/ Stop, ss)
  (ss, l@(Sym, _, "{") : ls) -> case span gappy ls of
    (ss', ls) -> case layLines Bracing ls of
      (br, ls) -> ((h, Bracy) :-! (map lex0 (ss ++ l : ss')) :-/ br, ls)
  (ss, l@(_, (_, x), _) : ls)
    | layStart g l -> case layLines (Indenting h x) (l : ls) of
        (de, ls) -> ((h, Denty x) :-! map lex0 ss :-/ de, ls)
    | otherwise -> ((h, Empty) :-! [] :-/ Stop, ss ++ l : ls)

layStart :: Gimmode -> Lex0 -> Bool
layStart (Indenting _ i) (_, (_, j), _) = j > i
layStart Bracing _ = True

layLines
  :: Gimmode
  -> [Lex0]  -- must ensure no leading space
  -> (Even [LexL] [LexL], [Lex0])
layLines g ls = case gimme g False ls of
  (_, ch, st, ls) -> case (g, ls) of
    (Indenting s i, l@(_, (_, j), _) : ls)
      | i == j -> case layLines g (l : ls) of
        (de, ls) -> (ch :-\ map lex0 st :-/ de, ls)
      | otherwise -> (ch :-\ [] :-/ Stop, st ++ l : ls)
    (Bracing, l@(Sym, _, "}") : ls) ->
      (ch :-\ map lex0 (st ++ [l]) :-/ Stop, ls)
    (Bracing, l@(Sym, _, ";") : ls) -> case span gappy ls of
      (su, ls) -> case layLines g ls of
        (br, ls) -> (ch :-\ map lex0 (st ++ l : su) :-/ br, ls)
    (_, ls) -> (ch :-\ [] :-/ Stop, st ++ ls)

lexPhase1 :: [Lex0] -> Bloc Line
lexPhase1 ls = case span gappy ls of
  (ss, ls) -> map lex0 ss :-/ uncurry trailing (layLines (Indenting "" 1) ls)
 where
  trailing Stop               rs = [] :-\ map lex0 rs :-/ Stop
  trailing (a :-\ b :-/ Stop) rs = (a :-\ (b ++ map lex0 rs) :-/ Stop)
  trailing (a :-\ b :-/ e)    rs = a :-\ b :-/ trailing e rs

brackety :: [LexL] -> [LexL]
brackety = go B0 B0 where
  go bz lz [] = dump bz (lz <>> []) where
    dump B0 ls = ls
    dump (bz :< (kz, k)) ls = dump bz (kz <>> (bad k : ls))
  go bz lz (l@(Sym, _, [o]) : ls) | o `elem` "([{" =
    go (bz :< (lz, l)) B0 ls
  go bz lz (l@(Sym, _, [c]) : ls) | c `elem` ")]}" =
    blat bz lz where
    blat B0 lz = go B0 (lz :< bad l) ls
    blat (bz :< (kz, k@(_, p, [o]))) lz
      | ma o c
      = go bz (kz :< (T (LB k (lz <>> []) l), p, "")) ls
      | otherwise -- bad
      = blat bz ((kz :< bad k) <> lz)
  go bz lz (l : ls) = go bz (lz :< l) ls

  ma '(' ')' = True
  ma '[' ']' = True
  ma '{' '}' = True
  ma _   _   = False

rfold :: (x -> t -> t) -> [x] -> t -> t
rfold t2t xs t = foldr t2t t xs

lout :: LexL -> String -> String
lout (T ((h,_) :-! b), _ , _) = (h ++) . bout b
lout (T (LB lo ls lc), _, _) = lout lo . rfold lout ls . lout lc
lout (_, _, s) = (s ++)

bout :: Bloc Line -> String -> String
bout (ls :-/ e) = rfold lout ls . case e of
  Stop -> id
  ls :-\ o -> rfold lout ls . bout o

askTokIn :: String -> String -> Bool
askTokIn a b = go (lexPhase0 a) (lexPhase0 b) where
  go as bs | pref as bs = True
  go as [] = False
  go as (_ : bs) = go as bs
  pref ((t, _, _) : as) bs | no t = pref as bs
  pref as ((t, _, _) : bs) | no t = pref as bs
  pref [] bs = True
  pref _ [] = False
  pref (a : as) (b : bs) = txt a == txt b && pref as bs
  no Spc = True
  no Cmm = True
  no _ = False