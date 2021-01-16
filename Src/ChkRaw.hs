module Ask.Src.ChkRaw where

import Data.List
import Data.Char
import qualified Data.Map as M
import Control.Arrow ((***))

import Debug.Trace

import Ask.Src.Thin
import Ask.Src.Bwd
import Ask.Src.LexAsk
import Ask.Src.RawAsk
import Ask.Src.Tm

track = trace

data Setup = Setup
  { introRules :: [Rule]
  , weirdRules :: [Rule]
  , fixities   :: FixityTable
  } deriving Show

byRules :: Setup -> [Rule]
byRules s = introRules s ++ weirdRules s

mySetup :: Setup
mySetup = Setup
  { introRules = myIntroRules
  , weirdRules = myWeirdRules
  , fixities   = myFixities
  }

myFixities :: FixityTable
myFixities = M.fromList
  [ ("&", (7, RAsso))
  , ("|", (6, RAsso))
  , ("->", (1, RAsso))
  ]

data Rule =
  (Pat, Pat) :<=
  [ Tm
  ]
  deriving Show

myIntroRules :: [Rule]
myIntroRules =
  [ (PC "&" [PM "a" mempty, PM "b" mempty], PC "AndI" []) :<=
    [ TC "prove" [TM "a" []]
    , TC "prove" [TM "b" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], PC "OrIL" []) :<=
    [ TC "prove" [TM "a" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], PC "OrIR" []) :<=
    [ TC "prove" [TM "b" []]
    ]
  , (PC "->" [PM "a" mempty, PM "b" mempty], PC "ImpI" []) :<=
    [ TC "given" [TM "a" [], TC "prove" [TM "b" []]]
    ]
  , (PC "True" [], PC "True" []) :<= []
  ]

myWeirdRules :: [Rule]
myWeirdRules =
  [ (PM "x" mempty, PC "Contradiction" []) :<=
    [ TC "given" [TC "->" [TM "x" [], TC "False" []],
      TC "prove" [TC "False" []]]
    ]
  ]

data TmR
  = My Tm
  | Our Tm Appl
  | Your Appl
instance Show TmR where
  show (My t) = show t
  show (Our t _) = show t
  show (Your (_, a)) = show a

my :: TmR -> Maybe Tm
my (My t) = Just t
my (Our t _) = Just t
my _ = Nothing

data Status
  = Junk Gripe
  | Keep
  | Need
  deriving (Show, Eq)

data Gripe
  = Surplus
  | Scope String
  | ByBadRule
  | ByAmbiguous
  | Mardiness
  deriving (Show, Eq)

passive :: Prove () Appl -> Prove Status TmR
passive (Prove g m () ps src) =
  Prove (Your g) (fmap Your m) Keep (map subPassive ps) src
subPassive :: SubProve () Appl -> SubProve Status TmR
subPassive ((srg, gs) ::- p) = (srg, map (fmap Your) gs) ::- passive p
subPassive (SubPGap ls)  = SubPGap ls
subPassive (SubPGuff ls) = SubPGuff ls

-- this type is highly provisional
chkProof
  :: Setup       -- a big record of gubbins
  -> Context     -- what do we know?
  -> TmR         -- the goal
  -> Method Appl -- the method
  -> [SubProve () Appl]  -- the subproofs
  -> ([LexL], [LexL])  -- source tokens (head, body)
  -> Prove Status TmR  -- the reconstructed proof

chkProof setup ga g m ps src = case my g of
  Just gt -> case m of
    Stub -> Prove g Stub Keep
      (map subPassive ps) src
    By r -> case scoApplTm ga r of
      Left x -> Prove g (By (Your r)) (Junk (Scope x))
        (map subPassive ps) src
      Right r@(Our rt _) -> case
        [ stan (mgh ++ mmn) ss
        | ((h, n) :<= ss) <- byRules setup
        , mgh <- mayl $ match mempty h gt
        , mmn <- mayl $ match mempty n rt
        ] of
        [ss] -> Prove g (By r) Keep (chkSubProofs setup ga ss ps) src
        sss -> Prove g (By r)
          (Junk (if null sss then ByBadRule else ByAmbiguous))
          (map subPassive ps) src
    From h -> case scoApplTm ga h of
      Left x -> Prove g (From (Your h)) (Junk (Scope x))
        (map subPassive ps) src
      Right h@(Our ht _) -> Prove g (From h) Keep
        (chkSubProofs setup ga (fromSubs setup ga gt ht) ps) src
  Nothing -> Prove g (fmap Your m) (Junk Mardiness)
    (map subPassive ps) src

-- checking subproofs amounts to validating them,
-- then checking which subgoals are covered,
-- generating stubs for those which are not,
-- and marking as surplus those subproofs which do
-- not form part of the cover
chkSubProofs
  :: Setup
  -> Context                    -- what do we know?
  -> [Tm]                       -- subgoals expected from rule
  -> [SubProve () Appl]         -- subproofs coming from user
  -> [SubProve Status TmR]      -- reconstruction
chkSubProofs setup ga ss ps = map squish qs ++ extra us where
  (qs, us) = cover ss $ map ((,) False . validSubProof setup ga) ps
  cover [] qs = (qs, [])
  cover (t : ts) qs = case cover1 t qs of
    Nothing -> case cover ts qs of
      (qs, ts) -> (qs, t : ts)
    Just qs -> cover ts qs
  cover1 :: Tm -> [(Bool, SubProve Status TmR)]
               -> Maybe [(Bool, SubProve Status TmR)]
  cover1 t [] = Nothing
  cover1 t ((b, p) : qs)
    | covers t p = Just ((True, p) : qs)
    | otherwise  = ((b, p) :) <$> cover1 t qs
  covers :: Tm -> SubProve Status TmR -> Bool
  covers t ((_, hs) ::- Prove g m Keep _ _) = case (subgoal (ga, t), my g) of
    (Just (ga, p), Just g) -> all (ga `gives`) hs && (g == p)
    _ -> False
  covers t _ = False
  squish :: (Bool, SubProve Status TmR) -> SubProve Status TmR
  squish (False, gs ::- Prove g m Keep ss src) = gs ::- Prove g m (Junk Surplus) ss src
  squish (_, q) = q
  extra :: [Tm] -> [SubProve Status TmR]
  extra [] = []
  extra (u : us) = case subgoal (ga, u) of
    Nothing -> extra us
    Just (ga, g)
      | gives ga (Given (My g)) -> extra us
      | otherwise -> need u : extra us
  need (TC "prove" [g]) = ([], []) ::- Prove (My g) Stub Need [] ([], [])
  need (TC "given" [h, u]) = case need u of
    (_, gs) ::- p -> ([], Given (My h) : gs) ::- p
    s -> s

subgoal :: (Context, Tm) -> Maybe (Context, Tm)
subgoal (ga, TC "given" [h, g]) = subgoal (ga :< Hyp h, g)
subgoal (ga, TC "prove" [g]) = Just (ga, g)
subgoal _ = Nothing

gives :: Context -> Given TmR -> Bool
gives ga (Given h) = case my h of
  Just h -> any (Hyp h ==) ga
  Nothing -> False

validSubProof
  :: Setup
  -> Context
  -> SubProve () Appl
  -> SubProve Status TmR
validSubProof setup ga ((srg, Given h : gs) ::- p@(Prove sg sm () sps src)) =
  case scoApplTm ga h of
    Left x -> (srg, map (fmap Your) (Given h : gs)) ::-
      Prove (Your sg) (fmap Your sm) (Junk (Scope x))
        (map subPassive sps) src
    Right h@(Our ht _) -> case validSubProof setup (ga :< Hyp ht) ((srg, gs) ::- p) of
      (srg, gs) ::- p -> (srg, Given h : gs) ::- p
      s -> s
validSubProof setup ga ((srg, []) ::- Prove sg sm () sps src) = case scoApplTm ga sg of
  Left x -> (srg, []) ::- Prove  (Your sg) (fmap Your sm) (Junk (Scope x))
    (map subPassive sps) src
  Right sg -> (srg, []) ::- chkProof setup ga sg sm sps src
validSubProof _ _ (SubPGap ls) = SubPGap ls
validSubProof _ _ (SubPGuff ls) = SubPGuff ls

fromSubs
  :: Setup
  -> Context
  -> Tm      -- goal
  -> Tm      -- fmla
  -> [Tm]
fromSubs setup ga g f = TC "prove" [f] : case
  [ (n, stan m ss)  -- ignoring n will not always be ok
  | ((h, n) :<= ss) <- introRules setup
  , m <- mayl $ match mempty h f
  ] of
  [(_, [s])] -> flop s g
  rs -> map (foldr wrangle (TC "prove" [g]) . snd) rs
 where
  flop (TC "prove" [p]) g = [TC "given" [p, TC "prove" [g]]]
  flop (TC "given" [h, s]) g = TC "prove" [h] : flop s g
  flop _ _ = [TC "prove" [g]] -- should not happen
  wrangle p g = TC "given" [wangle p, g]
  wangle (TC "given" [s, t]) = TC "->" [s, wangle t]
  wangle (TC "prove" [p]) = p
  wangle _ = TC "True" []


type Context = Bwd CxE

data CxE -- what sort of thing is in the context?
  = Hyp Tm
  | Var String
  deriving (Show, Eq)


applScoTm :: Appl -> (Context, TmR)
applScoTm a@(_, x) = (ga, Our t a) where
  (xs, t) = go x
  ga = B0 <>< map Var (nub xs)
  ge x (ga :< Var y) = if x == y then 0 else 1 + ge x ga
  ge x (ga :< _)     = ge x ga
  go ((t, _, y) :$$ ras) = case t of
      Lid -> (y : ys, TE (foldl (:$) (TV (ge y ga)) ts))
      _   -> (ys, TC y ts)
    where
    (ys, ts) = traverse (go . snd) ras

scoApplTm :: Context -> Appl -> Either String TmR
scoApplTm ga a@(_, t) = ((`Our` a)) <$> go t
  where
    go ((t, _, y) :$$ ras) = case t of
      Lid -> TE <$> ((foldl (:$) . TV) <$> ge y ga <*> as)
      _   -> TC y <$> as
      where as = traverse (go . snd) ras
    ge x (ga :< Var y) = if x == y then pure 0 else (1 +) <$> ge x ga
    ge x (ga :< _)     = ge x ga
    ge x B0            = Left x

mayl :: Maybe x -> [x]
mayl = foldMap return

data Spot = AllOK | RadSpot | Infix (Int, Either Assocy Assocy) | Arg deriving (Show, Eq)
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
  (ppEl setup ga RadSpot f ++ " :: " ++ ppTm setup ga Arg s)

pout :: Setup -> (Maybe WhereKind, Maybe Int) -> Context -> Prove Status TmR -> String
pout setup (mk, mc) ga p@(Prove g m s ps (h, b)) = case s of
  Keep -> rfold lout h "" ++ psout b ps
  Need -> "prove " ++ ppTmR setup ga AllOK g ++ " ?" ++ psout b ps
  Junk e -> fmat (case mk of { Nothing -> Dental 0; Just k -> k })
    [ "{- " ++ show e
    , rfold lout h . rfold lout b $ ""
    , "-}"
    ] ""
 where
  hdent = case (mc, h) of
    (Just c, _) -> c
    (_, (Key, (_, d), "prove") : _) -> d - 1
    _ -> 0
  psout :: [LexL] -> [SubProve Status TmR] -> String
  psout b ps = case span gappy b of
    (g, (T ((_,"where",gap) :-! m),_,_): ls) ->
      rfold lout g . ("where" ++) . rfold lout gap $ case whereKind hdent m of
        k@(Dental d) -> fmat k (ps >>= sub k) (rfold lout ls "")
        k@(Bracy pre semi post) -> "{" ++ rfold lout pre (fmat k (ps >>= sub k) (rfold lout ls ""))
    _ | null ps -> ""  -- rly?
    _ ->
      " where\n" ++ replicate (hdent + 2) ' ' ++
      fmat k (ps >>= sub k) ""
      where k = Dental (hdent + 2)
  fmat :: WhereKind -> [String] -> String -> String
  fmat (Dental d) [] = id
  fmat (Bracy _ _ _) [] = ("{" ++)
  fmat (Dental d) [s] = (s ++)
  fmat (Bracy _ _ post) [s] = (s ++) . rfold lout post . ("}" ++)
  fmat k@(Dental d) (s : ss) = (s ++) . ("\n" ++) . (replicate d ' ' ++) . fmat k ss
  fmat k@(Bracy _ semi _) (s : ss) = (s ++) . rfold lout semi . fmat k ss
  sub :: WhereKind -> SubProve Status TmR -> [String]
  sub k ((srg, gs) ::- Prove _ _ (Junk e) _ (h, b)) =
    ["{-" ++ show e, rfold lout srg (rfold lout h (rfold lout b "")), "-}"]
  sub k ((srg, gs) ::- p) = return $
    (if null srg then givs gs else rfold lout srg)
    (pout setup (Just k, mc) (fish ga gs) p)
    where
    mc = case span gappy srg of
      (_, (_, (_, x), _) : _) -> Just (x - 1)
      _ -> Nothing
  sub k (SubPGap ls) = [rfold lout ls ""]
  sub k (SubPGuff ls) = ["{- " ++ rfold lout ls " -}"]
  fish ga [] = ga
  fish ga (Given h : gs) = case my h of
    Nothing -> fish ga gs
    Just h -> fish (ga :< Hyp h) gs
  givs [] = id
  givs (g : gs) =
    ("given " ++) . (wallop g ++) . ((gs >>= ((", " ++) . wallop)) ++) . (" " ++)
    where
      wallop (Given g) = ppTmR setup ga AllOK g

filth :: String -> IO ()
filth s = mapM_ yuk (raw (fixities mySetup) s) where
  yuk (RawProof (Prove gr mr () ps src), _) =
    putStr . pout mySetup (Nothing, Nothing) ga $ chkProof mySetup ga g mr ps src where
    (ga, g) = applScoTm gr
  yuk (RawSewage, ls) = putStr $ "{- don't ask\n" ++ rfold lout ls "-}\n"
  yuk (_, ls) = putStr $ rfold lout ls ""