module Ask.Src.ChkRaw where

import Data.List
import Data.Char
import qualified Data.Map as M
import Control.Arrow ((***))
import Data.Bifoldable

import Debug.Trace

import Ask.Src.Thin
import Ask.Src.Bwd
import Ask.Src.OddEven
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Scoping
import Ask.Src.Printing
import Ask.Src.HardwiredRules

track = trace

type Anno =
  ( Status
  , Bool    -- is it proven?
  )

data Status
  = Junk Gripe
  | Keep
  | Need
  deriving (Show, Eq)

data Gripe
  = Surplus
  | Scope String
  | ByBadRule
  | NotGiven
  | ByAmbiguous
  | Mardiness
  deriving (Show, Eq)

passive :: Prove () Appl -> Prove Anno TmR
passive (Prove g m () ps src) =
  Prove (Your g) (fmap Your m) (Keep, False) (fmap subPassive ps) src
  
subPassive :: SubProve () Appl -> SubProve Anno TmR
subPassive ((srg, gs) ::- p) = (srg, map (fmap Your) gs) ::- passive p
subPassive (SubPGuff ls) = SubPGuff ls

surplus :: Prove () Appl -> Prove Anno TmR
surplus (Prove g m () ps src) =
  Prove (Your g) (fmap Your m) (Junk Surplus, True) (fmap subPassive ps) src
  
subSurplus :: SubProve () Appl -> SubProve Anno TmR
subSurplus ((srg, gs) ::- p) = (srg, map (fmap Your) gs) ::- surplus p
subSurplus (SubPGuff ls) = SubPGuff ls

-- this type is highly provisional
chkProof
  :: Setup       -- a big record of gubbins
  -> Context     -- what do we know?
  -> TmR         -- the goal
  -> Method Appl -- the method
  -> Bloc (SubProve () Appl)  -- the subproofs
  -> ([LexL], [LexL])  -- source tokens (head, body)
  -> Prove Anno TmR  -- the reconstructed proof

chkProof setup ga g m ps src = case my g of
  Just gt -> case m of
    Stub -> Prove g Stub (Keep, False)
      (fmap subPassive ps) src
    By r -> case scoApplTm ga r of
      Left x -> Prove g (By (Your r)) (Junk (Scope x), True)
        (fmap subPassive ps) src
      Right r@(Our rt _) -> case
        [ stan (mgh ++ mmn) ss
        | ((h, n) :<= ss) <- byRules setup
        , mgh <- mayl $ match mempty h gt
        , mmn <- mayl $ match mempty n rt
        ] of
        [ss] ->
          let ns = chkSubProofs setup ga ss ps
          in  Prove g (By r) (Keep, all happy ns) ns src
        sss -> Prove g (By r)
          (Junk (if null sss then ByBadRule else ByAmbiguous), True)
          (fmap subPassive ps) src
    From h -> case scoApplTm ga h of
      Left x -> Prove g (From (Your h)) (Junk (Scope x), True)
        (fmap subPassive ps) src
      Right h@(Our ht _) -> 
        let ns = chkSubProofs setup ga (fromSubs setup ga gt ht) ps
        in  Prove g (From h) (Keep, all happy ns) ns src
    MGiven -> if gives ga (Given g)
      then Prove g MGiven (Keep, True) (fmap subSurplus ps) src
      else Prove g MGiven (Junk NotGiven, True) (fmap subPassive ps) src
  Nothing -> Prove g (fmap Your m) (Junk Mardiness, True)
    (fmap subPassive ps) src

happy :: SubProve Anno TmR -> Bool
happy (_ ::- Prove _ _ (_, b) _ _) = b
happy _ = True
 
-- checking subproofs amounts to validating them,
-- then checking which subgoals are covered,
-- generating stubs for those which are not,
-- and marking as surplus those subproofs which do
-- not form part of the cover
chkSubProofs
  :: Setup
  -> Context                    -- what do we know?
  -> [Tm]                       -- subgoals expected from rule
  -> Bloc (SubProve () Appl)    -- subproofs coming from user
  -> Bloc (SubProve Anno TmR)   -- reconstruction
chkSubProofs setup ga ss ps = glom (fmap squish qs) (extra us) where
  (qs, us) = cover ss $ fmap ((,) False . validSubProof setup ga) ps
  cover [] qs = (qs, [])
  cover (t : ts) qs = case cover1 t qs of
    Nothing -> case cover ts qs of
      (qs, ts) -> (qs, t : ts)
    Just qs -> cover ts qs
  cover1 :: Tm -> Bloc (Bool, SubProve Anno TmR)
               -> Maybe (Bloc (Bool, SubProve Anno TmR))
  cover1 t (_ :-/ Stop) = Nothing
  cover1 t (g :-/ (b, p) :-\ qs)
    | covers t p = Just (g :-/ (True, p) :-\ qs)
    | otherwise  = (g :-/) <$> (((b, p) :-\) <$> cover1 t qs)
  covers :: Tm -> SubProve Anno TmR -> Bool
  covers t ((_, hs) ::- Prove g m (Keep, _) _ _) = case (subgoal (ga, t), my g) of
    (Just (ga, p), Just g) -> all (ga `gives`) hs && (g == p)
    _ -> False
  covers t _ = False
  squish :: (Bool, SubProve Anno TmR) -> SubProve Anno TmR
  squish (False, gs ::- Prove g m (Keep, _) ss src) =
    gs ::- Prove g m (Junk Surplus, True) ss src
  squish (_, q) = q
  extra :: [Tm] -> [SubProve Anno TmR]
  extra [] = []
  extra (u : us) = case subgoal (ga, u) of
    Nothing -> extra us
    Just (ga, g)
      | gives ga (Given (My g)) -> extra us
      | otherwise -> need u : extra us
  need (TC "prove" [g]) =
    ([], []) ::- Prove (My g) Stub (Need, False)
      ([] :-/ Stop) ([], [])
  need (TC "given" [h, u]) = case need u of
    (_, gs) ::- p -> ([], Given (My h) : gs) ::- p
    s -> s
  glom :: Bloc x -> [x] -> Bloc x
  glom (g :-/ p :-\ gps) = (g :-/) . (p :-\) . glom gps
  glom end = foldr (\ x xs -> [] :-/ x :-\ xs) end

subgoal :: (Context, Tm) -> Maybe (Context, Tm)
subgoal (ga, TC "given" [h, g]) = subgoal (ga :< Hyp h, g)
subgoal (ga, TC "prove" [g]) = Just (ga, g)
subgoal _ = Nothing

gives :: Context -> Given TmR -> Bool
gives ga (Given h) = case my h of
  Just h -> h == TC "True" [] ||
            any ((||) <$> (Hyp h ==) <*> (Hyp (TC "False" []) ==)) ga
  Nothing -> False

validSubProof
  :: Setup
  -> Context
  -> SubProve () Appl
  -> SubProve Anno TmR
validSubProof setup ga ((srg, Given h : gs) ::- p@(Prove sg sm () sps src)) =
  case scoApplTm ga h of
    Left x -> (srg, map (fmap Your) (Given h : gs)) ::-
      Prove (Your sg) (fmap Your sm) (Junk (Scope x), True)
        (fmap subPassive sps) src
    Right h@(Our ht _) -> case validSubProof setup (ga :< Hyp ht) ((srg, gs) ::- p) of
      (srg, gs) ::- p -> (srg, Given h : gs) ::- p
      s -> s
validSubProof setup ga ((srg, []) ::- Prove sg sm () sps src) = case scoApplTm ga sg of
  Left x -> (srg, []) ::- Prove  (Your sg) (fmap Your sm) (Junk (Scope x), True)
    (fmap subPassive sps) src
  Right sg -> (srg, []) ::- chkProof setup ga sg sm sps src
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

mayl :: Maybe x -> [x]
mayl = foldMap return

testChkProof :: String -> [Prove Anno TmR]
testChkProof = foldMap (bof . fst) . raw (fixities mySetup) where
  bof (RawProof (Prove gr mr () ps src)) = [chkProof mySetup ga g mr ps src] where
    (ga, g) = applScoTm gr
  bof _ = []

pout :: Setup -> Context -> LayKind -> Prove Anno TmR -> Odd String [LexL]
pout setup ga k p@(Prove g m (s, n) ps (h, b)) = let k' = scavenge b in case s of
  Keep ->
    (rfold lout (h `prove` n) . whereFormat b ps .
     format k' $ psout k' ps)
    :-/ Stop
  Need ->
    (("prove " ++) . (ppTmR setup ga AllOK g ++) . (" ?" ++) . whereFormat b ps .
     format k' $ psout k' ps)
    :-/ Stop
  Junk e ->
    ("{- " ++ show e) :-/ [] :-\
    (rfold lout h . rfold lout b $ "") :-/ [] :-\
    "-}" :-/ Stop
 where
   ((Key, p, s) : ls) `prove` n | elem s ["prove", "proven"] =
     (Key, p, "prove" ++ if n then "n" else "") : ls
   (l : ls) `prove` n = l : (ls `prove` n)
   [] `prove` n = [] -- should never happen
   
   psout :: LayKind -> Bloc (SubProve Anno TmR) -> Bloc String
   psout k (g :-/ Stop) = g :-/ Stop
   psout k (g :-/ SubPGuff [] :-\ h :-/ r) = psout k ((g ++ h) :-/ r)
   psout k (g :-/ p :-\ gpo) = g :-/ subpout k p `ocato` psout k gpo

   subpout :: LayKind -> SubProve Anno TmR -> Odd String [LexL]
   subpout _ (SubPGuff ls)
     | all gappy ls = rfold lout ls "" :-/ Stop
     | otherwise = ("{- " ++ rfold lout ls " -}") :-/ Stop
   subpout _ ((srg, gs) ::- Prove _ _ (Junk e, _) _ (h, b)) =
     ("{- " ++ show e) :-/ [] :-\
     (rfold lout srg . rfold lout h . rfold lout b $ "") :-/ [] :-\
     "-}" :-/ Stop
   subpout k ((srg, gs) ::- p) =
     case pout setup (fish ga gs) k p of
       p :-/ b ->
         (if null srg then givs gs else rfold lout srg) p :-/ b
    where
     fish ga [] = ga
     fish ga (Given h : gs) = case my h of
       Nothing -> fish ga gs
       Just h -> fish (ga :< Hyp h) gs
     givs [] = id
     givs (g : gs) =
       ("given " ++) . (wallop g ++) . ((gs >>= ((", " ++) . wallop)) ++) . (" " ++)
       where
         wallop (Given g) = ppTmR setup ga AllOK g
      
   whereFormat :: [LexL] -> Bloc x -> String -> String
   whereFormat ls xs pso = case span gappy ls of
     (g, (T (("where", k) :-! _), _, _) : rs) ->
       rfold lout g . ("where" ++) . (pso ++) $ rfold lout rs ""
     _ -> case xs of
       [] :-/ Stop -> ""
       _ -> " where" ++ pso

   format :: LayKind -> Bloc String -> String
   format k gso@(pre :-/ _) = case k of
     Denty d
       | not (null pre) && all horiz pre ->
         bracy True (";\n" ++ replicate d ' ') (embrace gso) ""
       | otherwise     -> denty ("\n" ++ replicate (d - 1) ' ') gso ""
     Bracy -> bracy True ("; ") gso ""
    where
     bracy :: Bool {-first?-} -> String -> Bloc String
        -> String -> String
     bracy b _ (g :-/ Stop)
       | null g    = (if b then (" {" ++) else id) . ("}" ++)
       | otherwise = rfold lout g
     bracy b sepa (g :-/ s :-\ r) =
       (if null g
          then ((if b then " {" else sepa) ++)
          else rfold lout g)
       . (s ++)
       . bracy False (if semic g then rfold lout g "" else sepa) r
     denty sepa (g :-/ Stop) = rfold lout g -- which should be empty
     denty sepa (g :-/ s :-\ r) =
       (if null g then (sepa ++) else rfold lout g) . (s ++) . denty sepa r

   scavenge
     :: [LexL]   -- first nonspace is "where" if input had one
     -> LayKind  -- to be used
   scavenge ls = case span gappy ls of
     (_, (T (("where", k) :-! _), _, _) : _) | k /= Empty -> k
     _ -> case k of
       Denty d -> Denty (d + 2)
       Bracy   -> Bracy

   horiz :: LexL -> Bool
   horiz (Ret, _, _) = False
   horiz (Cmm, _, s) = all (not . (`elem` "\r\n")) s
   horiz _ = True

   semic :: [LexL] -> Bool
   semic = go False where
     go b [] = b
     go b ((Cmm, _, _) : _) = False
     go b (g : ls) | gappy g = go b ls
     go False ((Sym, _, ";") : ls) = go True ls
     go _ _ = False

   embrace :: Bloc String -> Bloc String
   embrace (g :-/ Stop) = g :-/ Stop
   embrace (g :-/ s :-\ r) = mang g (++ [(Sym, (0,0), "{")]) :-/ s :-\ go r
     where
     go (h :-/ Stop) = mang h clos :-/ Stop
     go (g :-/ s :-\ h :-/ Stop) =
       mang g sepa :-/ s :-\ mang h clos :-/ Stop
     go (g :-/ s :-\ r) = mang g sepa :-/s :-\ go r
     mang [] f = []
     mang g  f = f g
     clos ls = (Sym, (0,0), "}") :ls
     sepa ls = (Sym, (0,0), ";") : ls ++ [(Spc, (0,0), " ")]

{-
defSepa :: LayKind -> String
defSepa (Denty d) = "\n" ++ replicate (d - 1) ' '
defSepa Bracy = "; "
defSepa Empty = ""

pout :: Setup -> LayKind -> Context -> Prove Status TmR -> String
pout setup k ga p@(Prove g m (s, n) ps (h, b)) = case s of
  Keep -> let (h', i) = tweak n h in rfold lout h' $ psout i b ps
  Need -> "prove " ++ ppTmR setup ga AllOK g ++ " ?" ++ psout b ps
  Junk e ->
    let sepa = case k of
          Bracy -> " "
          k     -> defSepa k  
    in "{- " ++ show e ++ sepa ++ rfold lout h . rfold lout b $ (sepa ++ "-}")
 where
  tweak True  ((Key, p, "prove") : ls) = ((Key, p, "proven") : ls, 1)
  tweak False ((Key, p, "proven") : ls) = ((Key, p, "prove") : ls, negate 1)
  tweak n [] = ([], 0)
  tweak n (l : ls) = (l : ls', i) where (ls', i) = tweak n ls
  psout :: Int -> [LexL] -> Bloc (SubProve Status TmR) -> String
  psout b ps = case span gappy b of
    (g, (T ((_, "where", k') :-! m),_,_): ls) ->
      let k'' = case k' of {Empty -> bump k; _ -> k'}
      rfold lout g . ("where" ++) .

{-
(replicate (hdent + 2) ' ' ++) $ (case whereKind hdent m of
        k@(Dental d) -> fmat k (ps >>= sub k)
        k@(Bracy pre semi post) -> ("{" ++) . rfold lout pre . fmat k (ps >>= sub k)
      )  (rfold lout gap . rfold lout ls $ "")
    _ | null ps -> rfold lout b ""
    _ ->
      " where\n" ++ replicate (hdent + 2) ' ' ++
      fmat k (ps >>= sub k) (rfold lout b "")
      where k = Dental (hdent + 2)
-}

  bump (Denty d) = Denty (d + 2)
  bump Bracy     = Bracy
  bump Empty     = Denty 1 -- shouldn't happen

  subs :: LayKind -> Bloc (SubProve Status TmR) -> Bloc String
  subs k
  

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
-}

filth :: String -> String
filth s = bifoldMap (($ "") . rfold lout) yuk (raw (fixities mySetup) s) where
  yuk (RawProof (Prove gr mr () ps src), _) =
    bifoldMap id (($ "") . rfold lout)
    . pout mySetup ga (Denty 1)
    $ chkProof mySetup ga g mr ps src
   where
    (ga, g) = applScoTm gr
  yuk (RawSewage, ls) = "{- don't ask\n" ++ rfold lout ls "-}\n"
  yuk (_, ls) = rfold lout ls ""

