------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.RawAsk                                       ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    DeriveFunctor
  , FlexibleInstances
#-}

module Ask.Src.RawAsk where

import Ask.Src.OddEven
import Ask.Src.Lexing
import Ask.Src.Parsing
import Ask.Src.Tm

import qualified Data.Map as M
import Control.Applicative
import Control.Monad


------------------------------------------------------------------------------
--  Raw Syntax Datatypes
------------------------------------------------------------------------------

data RawDecl
  = RawHeeHaw
  | RawModule String
  | RawSewage
  | RawFixity FixityTable
  | RawProp Appl (Bloc RawIntro)
  | RawData Appl [Appl]
  | RawSig Appl Appl
  | RawTest Appl (Maybe Appl)
  | RawProof (Make () Appl)
  deriving Show
  
data RawIntro
  = RawIntro
  { introPats :: [Appl]
  , rulePat   :: Appl
  , rulePrems :: Bloc ([Appl], Appl)
  } deriving Show

data Make a t
  = Make
  { making     :: Making
  , goal       :: t
  , method     :: Method t
  , annotation :: a
  , subproofs  :: Bloc (SubMake a t)
  , source     :: ([LexL], [LexL])
  }
  deriving (Functor)

data SubMake a t
  = ([LexL], [Given t]) ::- Make a t
  | SubPGuff [LexL]
  deriving (Functor)

data Making = Prf | Def deriving Eq
instance Show Making where
  show Prf = "prove"
  show Def = "define"
done :: Making -> Bool -> String
done m False = show m
done m True  = show m ++ case m of {Prf -> "n"; Def -> "d"}

data Method t
  = Stub
  | By t
  | From t
  | MGiven
  | Is t
  | Ind [String]
  deriving (Show, Functor)

data Given t
  = Given t
  deriving (Show, Functor)

data Assocy = LAsso | NAsso | RAsso deriving (Show, Eq)
type FixityTable = M.Map String (Int, Assocy)



------------------------------------------------------------------------------
--  Show instances which hide
------------------------------------------------------------------------------

instance (Show a, Show t) => Show (Make a t) where
  show p = concat
    [ show (making p), " "
    , show (goal p), " "
    , show (method p), " "
    , show (annotation p), "\n"
    , show (subproofs p)
    ]

instance (Show a, Show t) => Show (SubMake a t) where
  show ((_, gs) ::- p) = show gs ++ " |- " ++ show p
  show (SubPGuff ls) = "SubPGuff " ++ show ls


------------------------------------------------------------------------------
--  Lex and Parse
------------------------------------------------------------------------------

raw :: FixityTable -> String -> (FixityTable, Bloc (RawDecl, [LexL]))
raw fi input = (fo, fmap grok ls) where
  ls = lexAll input
  ft = newFixities ls
  fo = fi <> ft
  grok l = case parTok pDecl fo l of
    [(_, x, [])] -> (x, l)
    _ -> (RawSewage, l)

type PF = ParTok FixityTable

pDecl :: PF RawDecl
pDecl = good <* eol where
  good = RawHeeHaw <$ spc
     <|> RawModule <$ the Key "module" <*> spd (txt <$> kinda Uid)
           <* lol "where" (pure ())
     <|> RawFixity <$> (((,) <$> penv <*> mkFixity) >>= agree)
     <|> uncurry RawProp <$ the Key "prop" <*> pProp
     <|> uncurry RawData <$ the Key "data" <*> pData
     <|> RawSig <$> pAppl ["::", "="] <* spd (the Sym "::") <*> pAppl []
     <|> RawTest <$ (the Key "test" <|> the Key "tested") <* spc
           <*> pAppl ["="] <*>
           (Just <$ spd (the Sym "=") <*> pAppl [] <|> pure Nothing)
     <|> RawProof <$> pMake
  agree (ft, at) = at <$ guard (all id $ M.intersectionWith (==) at ft)

pProp :: PF (Appl, Bloc RawIntro)
pProp = do
    r@(_, h :$$ _) <- spd (pAppl [])
    is <- lol "where" (pIntro h) <|> pure ([] :-/ Stop)
    return (r, is)

pIntro :: LexL -> PF RawIntro
pIntro h = do
    the Key "prove"
    (_, g :$$ xs) <- spd (pAppl [])
    guard (txt h == txt g)
    the Key "by"
    r <- spd (pAppl [])
    ps <- lol "where"
             ((,) <$> (id <$ the Key "given" <* spc <*> sep (pAppl []) (spd (the Sym ","))
                          <* spc
                           <|> pure []) <*
                   the Key "prove" <* spc <*> pAppl [])
          <|> ([] :-/ Stop) <$ spc
    return $ RawIntro
      { introPats = xs, rulePat = r, rulePrems = ps }

pData :: PF (Appl, [Appl])
pData = (,) <$ spc <*> pAppl ["="] <* spd (the Sym "=") <*> sep (pAppl ["|"]) (spd (the Sym "|"))

pMake :: PF (Make () Appl)
pMake = do
  (top, (mk, go, me)) <- ext $ do
    mk <- pMaking
    spc
    go <- pAppl $ case mk of {Prf -> []; Def -> ["="]}
    spc
    me <- pMethod mk
    return (mk, go, me)
  (body, ps) <- ext (id <$ spc <*> pSubs)
  return $ Make
    { making     = mk
    , goal       = go
    , method     = me
    , annotation = ()
    , subproofs  = ps
    , source     = (top, body)
    }
  where
  pMaking = Prf <$ (the Key "prove" <|> the Key "proven")
        <|> Def <$ (the Key "define" <|> the Key "defined")
  pMethod mk
    =   Stub <$ the Sym "?"
    <|> From <$ the Key "from" <* spc <*> pAppl []
    <|> case mk of
           Prf -> By   <$ the Key "by"   <* spc <*> pAppl []
              <|> MGiven <$ the Key "given"
           Def -> Is <$ the Sym "=" <* spc <*> pAppl []
              <|> Ind <$ the Key "inductively" <* spc <*>
                    sep (txt <$> kinda Lid) (spd (the Sym ","))
  pSubs = lol "where" pSub <|> pure ([] :-/ Stop)
  pSub = ((::-) <$> ext (pGivens <* spc) <*> pMake <* spc <* eol)
      ?> ((SubPGuff . fst) <$> ext (many (eat Just) <* eol))
  pGivens
    =   id <$ the Key "given" <* spc <*> sep (Given <$> pAppl []) (spd (the Sym ","))
    <|> pure []

newFixities :: Bloc [LexL] -> FixityTable
newFixities = foldMap (glom . parTok mkFixity mempty) where
  glom [(_,t,_)] = t
  glom _ = M.empty

mkFixity :: PF FixityTable
mkFixity = actual ?> pure M.empty where
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
  fixl _ = Nothing
  oppo :: PF String
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

type Appl = ([LexL], Appl')
data Appl' = LexL :$$ [Appl]

instance Show Appl' where
  show ((_,_,f) :$$ las) = f ++ show (map snd las)

($$) :: Appl' -> [Appl] -> Appl'
(h :$$ as) $$ bs = h :$$ (as ++ bs)

instance MDep Appl where
  mDep x (_, (_, _, y) :$$ as) = x == y || any (mDep x) as

-- FIXME: support tuples but not by treating comma as infix
pAppl :: [String] -- , and ` are already not allowed to be infix
                  -- but sometimeswe have other *top-level* exceptions
                  -- e.g., in data decls
      -> PF Appl
pAppl nae = ext $ pAppl' nae
pAppl' :: [String] -> PF Appl'
pAppl' nae = penv >>= gimme where
 gimme ftab = go nae where
  go :: [String] -> PF Appl'
  go nae = start nae (-1, NAsso)
  fixity :: LexL -> (Int, Assocy)
  fixity (_, _, s) = case M.lookup s ftab of
    Nothing -> (9, LAsso)
    Just f  -> f
  start :: [String] -> (Int, Assocy) -> PF Appl'
  start nae f = (ext $ (($$) <$> wee nae <*> many (id <$ spc <*> ext (wee nae))))
                >>= more nae f (maxBound, NAsso)
  wee :: [String] -> PF Appl'
  wee nae = (:$$ []) <$>
     (kinda Uid <|> kinda Lid <|>
      kinda Num <|> kinda Str <|> kinda Chr <|>
      brk '(' (spd (iop [])))
    <|> tup <$> ext (brk '(' (sep (ext (go [])) (spd (the Sym ","))))
  iop :: [String] -> PF LexL
  iop nae = (kinda Sym >>= \ l@(_, _, s) -> guard (not $ elem s (nae ++ ["`", ","])) >> return l)
    <|> id <$ the Sym "`" <*> (kinda Uid <|> kinda Lid) <* the Sym "`"
  more :: [String]
       -> (Int, Assocy) -- working to the right of this
       -> (Int, Assocy) -- we've got this
       -> Appl
       -> PF Appl'
  more nae (i, a) (j, b) (ls, e) = (<|> pure e) $ do
    (rs, (kc, e)) <- ext $ do
      spc
      o <- iop nae
      let (k, c) = fixity o
      guard (k > i || k == i && a == RAsso && c == RAsso)
      guard (k < j || k == j && b == LAsso && c == LAsso)
      spc
      f <- ext $ start nae (k, c)
      return ((k, c), o :$$ [(ls, e), f])
    more nae (i, a) kc (ls ++ rs, e)
  tup :: ([LexL], [Appl]) -> Appl'
  tup (_, [(_, x)]) = x
  tup (ls, las) = (Uid, ptup ls, stup (length las)) :$$ las where
    stup 0 = "()"
    stup n = "(" ++ replicate (n - 1) ',' ++ ")"
    ptup ((_, p, _) : _) = p
    ptup [] = (0, 0) -- but this should never happen, right?
