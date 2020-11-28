module RawAsk where

import Bwd
import LexAsk
import ParTok

import qualified Data.Map as M
import Control.Applicative
import Control.Monad

data RawDecl
  = RawHeeHaw
  | RawModule String
  | RawSewage
  | RawFixity FixityTable
  | RawProp Appl [RawIntro]
  deriving Show

pDecl :: FixityTable -> ParTok RawDecl
pDecl ft = (good <* eol) ?> (bad <* eol) where
  good = RawHeeHaw <$ spc
     <|> RawModule <$ the Key "module" <*> spd (txt <$> kinda Uid)
           <* lol "where" (pure ())
     <|> RawFixity <$> (fixity >>= agree)
     <|> prop
  bad = RawSewage <$ many (eat Just)
  agree at = at <$ guard (all id $ M.intersectionWith (==) at ft)
  prop = do
    the Key "prop"
    r@(h :$ _) <- spd (pAppl ft)
    is <- lol "where" (pIntro h) <|> [] <$ spc
    return $ RawProp r is
  pIntro h = do
    the Key "prove"
    g :$ xs <- spd (pAppl ft)
    guard (txt h == txt g)
    the Key "by"
    r <- spd (pAppl ft)
    ps <- lol "where"
             (spd ((,) <$> (id <$ the Key "given" <*> sep (pAppl ft) (the Sym ",")
                           <|> [] <$ spc) <*
                   the Key "prove" <*> spd (pAppl ft)))
          <|> [] <$ spc
    return $ RawIntro
      { introPats = map snd xs, rulePat = r, rulePrems = ps }

data RawIntro
  = RawIntro
    { introPats :: [Appl]
    , rulePat   :: Appl
    , rulePrems :: [([Appl], Appl)]
    } deriving Show

data Assocy = LAsso | NAsso | RAsso deriving (Show, Eq)
type FixityTable = M.Map String (Int, Assocy)

getFixities :: [[LexL]] -> FixityTable
getFixities = foldMap (glom . parTok fixity) where
  glom [(_,t,_)] = t
  glom _ = M.empty

fixity :: ParTok FixityTable
fixity = actual ?> pure M.empty where
  actual = mkTable <$>
    (LAsso <$ the Key "infixl"
     <|> NAsso <$ the Key "infix"
     <|> RAsso <$ the Key "infixr")
    <*> spd (eat fixl <|> pure 9)
    <*> ((:) <$> spd oppo <*> many (id <$ the Sym "," <*> spd oppo))
    <* eol
  fixl :: LexL -> Maybe Int
  fixl (Num, _, s) = case read s of
    l | 0 <= l && l <= 9 -> Just l
    _ -> Nothing
  oppo :: ParTok String
  oppo = id <$ the Sym "`" <*> eat lust <* the Sym "`"
     <|> eat sop
  lust :: LexL -> Maybe String
  lust (Uid, _, s) = Just s
  lust (Lid, _, s) = Just s
  lust _           = Nothing
  sop :: LexL -> Maybe String
  sop (Sym, _, s) | not (s `elem` ["`",","]) = Just s
  sop _ = Nothing
  mkTable :: Assocy -> Int -> [String] -> FixityTable
  mkTable a i xs = M.fromList [(x, (i, a)) | x <- xs]

data Appl = LexL :$ [([LexL], Appl)] deriving Show

($$) :: Appl -> [([LexL], Appl)] -> Appl
(h :$ as) $$ bs = h :$ (as ++ bs)

pAppl :: FixityTable -> ParTok Appl
pAppl ftab = go where
  go :: ParTok Appl
  go = start (-1, NAsso)
  fixity :: LexL -> (Int, Assocy)
  fixity (_, _, s) = case M.lookup s ftab of
    Nothing -> (9, LAsso)
    Just f  -> f
  start :: (Int, Assocy) -> ParTok Appl
  start f = (spd . ext $ (($$) <$> wee <*> many (spd . ext $ wee))) >>= more f (maxBound, NAsso)
  wee :: ParTok Appl
  wee = (:$ []) <$>
     (kinda Uid <|> kinda Lid <|>
      kinda Num <|> kinda Str <|> kinda Chr <|>
      brk '(' (spd iop))
    <|> brk '(' go
  iop :: ParTok LexL
  iop = (kinda Sym >>= \ l@(_, _, s) -> guard (s /= "`") >> return l)
    <|> id <$ the Sym "`" <*> (kinda Uid <|> kinda Lid) <* the Sym "`"
  more :: (Int, Assocy) -- working to the right of this
       -> (Int, Assocy) -- we've got this
       -> ([LexL], Appl)
       -> ParTok Appl
  more (i, a) (j, b) (ls, e) = (<|> pure e) $ do
    (rs, (kc, e)) <- ext $ do
      spc
      o <- iop
      let (k, c) = fixity o
      guard (k > i || k == i && a == RAsso && c == RAsso)
      guard (k < j || k == j && b == LAsso && c == LAsso)
      spc
      f <- ext $ start (k, c)
      return ((k, c), o :$ [(ls, e), f])
    more (i, a) kc (ls ++ rs, e)
