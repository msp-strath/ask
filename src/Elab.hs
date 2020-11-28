module Elab where

import Bwd
import LexAsk

import qualified Data.Map as M
import Control.Applicative
import Control.Monad

import Tm
import ParTok

data Decl
  = DeclInfix
      Assocy     -- associativity
      Int        -- fixity level
      [String]   -- operators
  | DeclProp
      String
      (Tel ())
      [Intro]
  deriving Show

data Intro = (Pat, Pat) :<=: [Tel Tm] deriving Show

data Assocy = LAsso | NAsso | RAsso deriving (Show, Eq)
type FixityTable = M.Map String (Int, Assocy)

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
    
    
myfix :: FixityTable
myfix = M.fromList [("+", (4, LAsso)), ("->", (3, RAsso))]