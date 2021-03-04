{-# LANGUAGE TupleSections, LambdaCase, PatternSynonyms #-}

module Ask.Src.ChkRaw where

import Data.List hiding ((\\))
import Data.Char
import Control.Arrow ((***))
import Data.Bifoldable
import Control.Applicative
import Data.Traversable
import Control.Monad
import Data.Foldable

import Debug.Trace

import Ask.Src.Hide
import Ask.Src.Thin
import Ask.Src.Bwd
import Ask.Src.OddEven
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Context
import Ask.Src.Typing
import Ask.Src.Proving
import Ask.Src.Printing
import Ask.Src.HardwiredRules
import Ask.Src.Progging

tracy = trace

type Anno =
  ( Status
  , Bool    -- is it proven?
  )

data Status
  = Junk Gripe
  | Keep
  | Need
  deriving Show

passive :: Make () Appl -> Make Anno TmR
passive (Make k g m () ps src) =
  Make k (Your g) (fmap Your m) (Keep, False) (fmap subPassive ps) src
  
subPassive :: SubMake () Appl -> SubMake Anno TmR
subPassive ((srg, (ds, gs)) ::- p) = (srg, (ds, map (fmap Your) gs)) ::- passive p
subPassive (SubPGuff ls) = SubPGuff ls

surplus :: Make () Appl -> Make Anno TmR
surplus (Make k g m () ps src) =
  Make k (Your g) (fmap Your m) (Junk Surplus, True) (fmap subPassive ps) src
  
subSurplus :: SubMake () Appl -> SubMake Anno TmR
subSurplus ((srg, (ds, gs)) ::- p) = (srg, (ds, map (fmap Your) gs)) ::- surplus p
subSurplus (SubPGuff ls) = SubPGuff ls

chkProg
  :: Proglem
  -> Appl
  -> Method Appl -- the method
  -> Bloc (SubMake () Appl)  -- the subproofs
  -> ([LexL], [LexL])  -- source tokens (head, body)
  -> AM (Make Anno TmR)  -- the reconstructed proof
chkProg p gr mr ps src@(h,b) = do
  push ExpectBlocker
  m <- case mr of
    Stub b -> pure $ Stub b
    Is a -> do
      doorStop
      True <- tracy ("IS " ++ show a ++ " ?") $ return True
      ga <- gamma
      for (paranoia ga []) $ \ x -> push $ RecShadow x
      traverse push (localCx p)
      a@(Our t _) <- elabTmR (rightTy p) a
      True <- tracy ("IS SO " ++ show t) $ return True
      (PC _ ps, sb) <- patify $ TC "" (map fst (leftImpl p ++ leftSatu p ++ leftAppl p))
      True <- tracy ("PATIFIED " ++ show ps ++ show sb) $ return True
      de <- doorStep
      pushOutDoor $ (fNom p, ps) :=:
        rfold e4p sb (discharge de t ::: discharge de (rightTy p))
      pure (Is a)
    From a@(_, ((_, _, x) :$$ as)) -> do
      doorStop
      traverse push (localCx p)
      (e, _) <- elabSyn EXP x as
      doorStep
      TE (TP (xn, Hide ty)) <- return (upTE e)
      tels <- conSplit PAT ty
      traverse (expect xn ty p) tels
      pure (From (Our (TE e) a))
    Ind [] -> gripe EmptyInductively
    Ind xs -> do
      p <- inductively p xs
      push (Expect p)
      pure $ Ind xs
    _ -> gripe FAIL
  (ns, b) <- chkSubProofs ps
  pop $ \case {ExpectBlocker -> True; _ -> False}
  let defined = case m of {Stub _ -> False; _ -> all happy ns}
  return $ Make Def (Your gr) m (Keep, b && defined) ns src
 where
  paranoia :: Bwd CxE -> [String] -> [String]
  paranoia B0 defs = []
  paranoia (ga :< Defined f) defs = paranoia ga (f : defs)
  paranoia (ga :< Declare u _ _) defs | not (u `elem` defs) =
    u : paranoia ga defs
  paranoia (ga :< _) defs = paranoia ga defs
  expect :: Nom -> Tm -> Proglem -> (Con, Tel) -> AM ()
  expect xn ty p (c, tel) = do
    (de, sb) <- wrangle (localCx p)
    push . Expect $ sbpg sb (p {localCx = de})
   where
    wrangle B0 = gripe FAIL
    wrangle (ga :< (Bind (yn, _) (User y))) | yn == xn = do
      (ga, xs) <- bungle ga [] B0 y tel
      return (ga, [(xn, TC c xs ::: ty)])
    wrangle (ga :< z) = do
      (ga, sb) <- wrangle ga
      case z of
        Hyp b h -> return (ga :< Hyp b (rfold e4p sb h), sb)
        Bind (yn, Hide ty) k -> do
          let yp = (yn, Hide (rfold e4p sb ty))
          return (ga :< Bind yp k, (yn, TP yp) : sb)
        z -> return (ga :< z, sb) 
    bungle ga sch xz y (Pr hs) = do
      zs <- for sch $ \ ((x, s), _) -> do
        xn <- fresh (y ++ x)
        return (x, xn, s)
      let m = [ (z, TE (TP (zn, Hide (stan m s))))
              | (z, zn, s) <- zs
              ]
      return (foldl glom ga m <>< map (Hyp True) (stan m hs), stan m (xz <>> []))
     where
      glom ga (z, TE (TP xp)) = ga :< Bind xp (User z)
      glom ga _ = ga
    bungle ga sch xz y (Ex a b) = do
      xn <- fresh ""
      let xp = (xn, Hide a)
      (ga, xs) <- bungle (ga :< Bind xp (User "")) sch xz y (b // TP xp)
      return (ga, TE (TP xp) : xs)
    bungle ga sch xz y ((x, s) :*: tel) =
      bungle ga (topInsert ((x, s), ()) sch) (xz :< TM x []) y tel
    sbpg :: [(Nom, Syn)] -> Proglem -> Proglem
    sbpg sb (Proglem de f u li ls la ty) =
      Proglem de f u
        (rfold e4p sb li)
        (rfold e4p sb ls)
        (rfold e4p sb la)
        (rfold e4p sb ty)

-- this type is highly provisional
chkProof
  :: TmR         -- the goal
  -> Method Appl -- the method
  -> Bloc (SubMake () Appl)  -- the subproofs
  -> ([LexL], [LexL])  -- source tokens (head, body)
  -> AM (Make Anno TmR)  -- the reconstructed proof

chkProof g m ps src = do
  ga <- filter (\case {Bind _ _ -> True; _ -> False}) <$> ((<>> []) <$> gamma)
  True <- tracy ("OHAI: " ++ show g ++ " " ++ show m ++ "\n" ++ show ga) $ return True
  cope go junk $ \ p -> do
    ga <- filter (\case {Bind _ _ -> True; _ -> False}) <$> ((<>> []) <$> gamma)
    True <- tracy ("KTHXBAI: " ++ show p ++ "\n" ++ show ga) $ return True
    return p
 where
  junk gr = return $ Make Prf g (fmap Your m) (Junk gr, True)
    (fmap subPassive ps) src
  go = case my g of
    Just gt -> do
      (m, b0) <- case m of
        Stub b -> pure $ (Stub b, False)
        By r -> (,True) <$> By <$> (gt `by` r)
        From h@(_, (t, _, _) :$$ _)
          | elem t [Uid, Sym] -> do
            ht <- elabTm EXP Prop h
            demand (PROVE ht)
            fromSubs gt ht
            return (From (Our ht h), True)
        From h@(_, (Lid, _, x) :$$ []) -> what's x >>= \case
          Right (e@(TP xp), ty) -> do
            ty <- hnf ty
            cts <- conSplit PAT ty
            (From (Our (TE e) h), True) <$
              traverse (splitProof xp ty gt) cts
          _ -> gripe $ FromNeedsConnective h
        From h -> gripe $ FromNeedsConnective h
        Ind [] -> gripe EmptyInductively
        Ind xs -> do
          indPrf gt xs
          return $ (Ind xs, True)
        MGiven -> hnf gt >>= \case
          TC "=" [ty, lhs, rhs] ->
            (MGiven,) <$> (given (TC "=" [ty, rhs, lhs])
                       <|> given (TC "=" [ty, lhs, rhs]))
          _ -> (MGiven,) <$> given gt
        Tested b -> hnf gt >>= \case
          TC "=" [ty, lhs, rhs] -> (Tested b, True) <$ tested ty lhs rhs
          _ -> gripe $ TestNeedsEq gt
        Under f -> hnf gt >>= \case
          TC "=" [ty, lhs, rhs] -> (Under f, True) <$ under lhs rhs f
          _ -> gripe $ UnderNeedsEq gt
      (ns, b1) <- chkSubProofs ps
      let proven = case m of {Stub _ -> False; _ -> all happy ns}
      return $ Make Prf g m (Keep, b0 && b1 && proven) ns src
    Nothing -> return $ Make Prf g (fmap Your m) (Junk Mardiness, True)
      (fmap subPassive ps) src

happy :: SubMake Anno TmR -> Bool
happy (_ ::- Make _ _ _ (_, b) _ _) = b
happy _ = True


-- checking subproofs amounts to validating them,
-- then checking which subgoals are covered,
-- generating stubs for those which are not,
-- and marking as surplus those subproofs which do
-- not form part of the cover
chkSubProofs
  :: Bloc (SubMake () Appl)         -- subproofs coming from user
  -> AM (Bloc (SubMake Anno TmR)
         , Bool {-no hidden deps-})   -- reconstruction
chkSubProofs ps = do
  ss <- demands
  (qs, us) <- traverse (validSubProof ss) ps >>= cover ss
  True <- tracy ("COVER " ++ show (qs, us)) $ return True
  eps <- gamma >>= sprog
  (vs, b) <- extra us
  return (glom (fmap squish qs) (eps ++ vs), b)
 where
  cover
    :: [Subgoal]  -- subgoals to cover
    -> Bloc (Bool, SubMake Anno TmR)  -- (used yet?, subproof)
    -> AM (Bloc (Bool, SubMake Anno TmR)  -- ditto
          , [Subgoal]                      -- undischarged subgoals
          )
  cover [] qs = return (qs, [])
  cover (t : ts) qs = cope (cover1 t qs)
    (\ _ -> cover ts qs >>= \ (qs, ts) -> return (qs, t : ts))
    $ cover ts
  cover1 :: Subgoal -> Bloc (Bool, SubMake Anno TmR)
         -> AM (Bloc (Bool, SubMake Anno TmR))
  cover1 t (_ :-/ Stop) = gripe FAIL
  cover1 t (g :-/ (b, p) :-\ qs) = cope (covers t p)
    (\ _ -> ((g :-/) . ((b, p) :-\ )) <$> cover1 t qs)
    $ \ _ -> return $ (g :-/ (True, p) :-\ qs)
  covers :: Subgoal -> SubMake Anno TmR -> AM ()
  covers sg sp = do
    doorStop
    True <- tracy ("COVERS: " ++ show sg ++ " ?\n" ++ show sp) $ return True
    go sg sp
    True <- tracy ("HAPPY: " ++ show sg ++ " ?\n" ++ show sp) $ return True
    doorStep
    return ()
   where
    go t ((_, (_, hs)) ::- Make Prf g m (Keep, _) _ _) = subgoal t $ \ t -> do
      g <- mayhem $ my g
      traverse smegUp (g : [h | Given x <- hs, Just h <- [my x]])
      traverse ensure hs
      True <- tracy ("COVERS " ++ show (g, t)) $ return True
      cope (unify Prop g t)
        (\ gr -> do
          True <- tracy "NOPE" $ return True
          gripe gr)
        return
      True <- tracy "YEP" $ return True        
      return ()
    go _ _ = gripe FAIL
    ensure (Given h) = mayhem (my h) >>= given
  squish :: (Bool, SubMake Anno TmR) -> SubMake Anno TmR
  squish (False, gs ::- Make k g m (Keep, _) ss src) =
    gs ::- Make k g m (Junk Surplus, True) ss src
  squish (_, q) = q
  sprog :: Context -> AM [SubMake Anno TmR]
  sprog ga = do
    (ga, ps) <- go ga []
    setGamma ga
    return ps
   where
    go :: Context -> [SubMake Anno TmR] -> AM (Context, [SubMake Anno TmR])
    go B0 ps = return (B0, ps)
    go ga@(_ :< ExpectBlocker) ps = return (ga, ps)
    go (ga :< Expect p) ps = go ga (blep p : ps)
    go (ga :< z) ps = ((:< z) *** id) <$> go ga ps
    blep :: Proglem -> SubMake Anno TmR
    blep p = ([], ([], [])) ::- -- bad hack on its way!
      Make Def (My (TC (uName p) (fst (frob [] (map fst (leftSatu p ++ leftAppl p))))))
        (Stub True) (Need, False) ([] :-/ Stop) ([], [])
      where
        frob zs [] = ([], zs)
        frob zs (TC c ts : us) = case frob zs ts of
          (ts, zs) -> case frob zs us of
            (us, zs) -> (TC c ts : us, zs)
        frob zs (TE (TP (x, _)) : us) = let
            y = case foldMap (dubd x) (localCx p) of
                  [y] -> y
                  _   -> fst (last x)
            z = grob (krob y) Nothing zs
          in case frob (z : zs) us of
            (us, zs) -> (TC z [] : us, zs)
        krob [] = "x"
        krob (c : cs)
          | isLower c = c : filter isIdTaily cs
          | isUpper c = toLower c : filter isIdTaily cs
          | otherwise = krob cs
        grob x i zs = if elem y zs then grob x j zs else y where
          (y, j) = case i of
            Nothing -> (x, Just 0)
            Just n -> (x ++ show n, Just (n + 1))
        dubd xn (Bind (yn, _) (User y)) | xn == yn = [y]
        dubd xn _ = []

  extra :: [Subgoal] -> AM ([SubMake Anno TmR], Bool)
  extra [] = return ([], True)
  extra (u : us) = cope (subgoal u obvious)
    (\ _ -> do
      u <- need u
      (us, b') <- extra us
      return (u : us, False))
    $ \ b -> do
      (us, b') <- extra us
      return (us, b && b')
  obvious s@(TC "=" [ty, lhs, rhs])
    =   given s
    <|> given (TC "=" [ty, rhs, lhs])
    <|> True <$ equal ty (lhs, rhs)
    <|> given FALSE
  obvious s
    =   given s
    <|> given FALSE
    <|> True <$ equal Prop (s, TRUE)
            
  need (PROVE g) = return $
    ([], ([], [])) ::- Make Prf (My g) (Stub True) (Need, False)
      ([] :-/ Stop) ([], [])
  need (GIVEN h u) = need u >>= \case
    (_, (ds, gs)) ::- p -> return $ ([], (ds, Given (My h) : gs)) ::- p
    s -> return s
  need (EVERY s b) = ("x", s) |:- \ x@(TP (xn, _)) ->
    need (b // x)
  glom :: Bloc x -> [x] -> Bloc x
  glom (g :-/ p :-\ gps) = (g :-/) . (p :-\) . glom gps
  glom end = foldr (\ x xs -> [] :-/ x :-\ xs) end

subgoal :: Subgoal -> (Tm -> AM x) -> AM x
subgoal (GIVEN h g) k = h |- subgoal g k
subgoal (PROVE g) k = k g
subgoal (EVERY t b) k = ("", t) |:- \ e -> subgoal (b // e) k

validSubProof
  :: [Subgoal] -- sneakily peek at what we want
  -> SubMake () Appl
  -> AM (Bool, SubMake Anno TmR)
validSubProof sgs sps = do
  True <- tracy ("VSUB: " ++ show sps) $ return True
  push ImplicitQuantifier -- cheeky!
  (b, m)  <- go sps
  ga <- gamma
  (ga, ds, us) <- jank ga
  True <- tracy ("JANK: " ++ show us) $ return True
  setGamma ga
  return (b, splott us ds m)
 where
  go ((srg, (ds, Given h : gs)) ::- p@(Make k sg sm () sps src)) =
    cope (elabTm EXP Prop h)
      (\ gr -> return $ (False, (srg, (ds, map (fmap Your) (Given h : gs))) ::-
        Make k (Your sg) (fmap Your sm) (Junk gr, True)
          (fmap subPassive sps) src))
      $ \ ht -> do
        (b, (srg, (ds, gs)) ::- p) <- ht |- go ((srg, (ds, gs)) ::- p)
        return $ (b, (srg, (ds, Given (Our ht h) : gs)) ::- p)
  go ((srg, (ds, [])) ::- Make Prf sg sm () sps src) =
    cope (elabTmR Prop sg)
      (\ gr -> return $ (False, (srg, (ds, [])) ::- Make Prf (Your sg) (fmap Your sm)
        (Junk gr, True) (fmap subPassive sps) src))
      $ \ sg -> (False, ) <$> (((srg, (ds, [])) ::-) <$> chkProof sg sm sps src)
  go ((srg, (ds, [])) ::- Make Def sg@(_, (_, _, f) :$$ as) sm () sps src) = do
    p <- gamma >>= expected f as
    True <- tracy ("FOUND " ++ show p) $ return True
    True <- gamma >>= \ ga -> tracy (show ga) $ return True
    (True,) <$> (((srg, (ds, [])) ::-) <$> chkProg p sg sm sps src)
   where
    expected f as B0 = gripe Surplus
    expected f as (ga :< z) = do
      True <- tracy ("EXP " ++ show f ++ show as ++ show z) $ return True
      cope (do
        Expect p <- return z
        dubStep p f as
        )
        (\ gr -> expected f as ga <* push z)
        (<$ setGamma ga)
  go (SubPGuff ls) = return $ (False, SubPGuff ls)
  jank (ga :< ImplicitQuantifier) = return (ga, [], [])
  jank (ga :< Bind (x, Hide ty) k) = do
    (ga, ds, us) <- jank ga
    ty <- norm ty
    case k of
      Defn t -> do
        t <- norm t
        return (ga, (x, rfold e4p ds (t ::: ty)) : ds, us)
      User y -> return (ga, (x, TP (x, Hide ty)) : ds, (x, y) : us)
      _ -> return (ga, (x, TP (x, Hide ty)) : ds, us)
  jank (ga :< z) = do
    (ga, ds, us) <- jank ga
    return (ga :< z, ds, us)
  jank ga = return (ga, [], [])
  splott us ds ((ls, (vs, hs)) ::- Make mk g me a sps src) =
    ((ls, (vs ++ us, [Given (rfold e4p ds h) | Given h <- hs])) ::- 
     Make mk (rfold e4p ds g) me a sps src)
  splott _ _ s = s

fromSubs
  :: Tm      -- goal
  -> Tm      -- fmla
  -> AM ()
fromSubs g f = hnf f >>= \case
  q@(TC "=" [ty, lhs, rhs]) -> do
    ty <- norm ty
    lhs' <- hnf lhs
    rhs' <- hnf rhs
    case (ty, lhs', rhs') of
      (TC d ss, TC c rs, TC e ts)
        | c /= e -> flip (cope (isDataType d)) return $ \ _ ->
           fred . GIVEN q $ PROVE g
        | otherwise -> ginger B0 [(ty, (lhs, rhs))] g
      (_, TE (TP (xn, _)), _) ->
           fred $ PROVE (e4p (xn, rhs ::: ty) g)
      (_, _, TE (TP (xn, _))) ->
           fred $ PROVE (e4p (xn, lhs ::: ty) g)
      _ -> fred . GIVEN q $ PROVE g
  f -> map snd {- ignorant -} <$> invert f >>= \case
    [[s]] -> flop s g
    rs -> mapM_ (fred . foldr (GIVEN . propify) (PROVE g)) rs
 where
  flop (PROVE p)   g = fred . GIVEN p $ PROVE g
  flop (GIVEN h s) g = do
    fred $ PROVE h
    flop s g
  propify (GIVEN s t) = s :-> propify t
  propify (PROVE p)   = p

ginger :: Bwd Tm -> [(Tm, (Tm, Tm))] -> Tm -> AM ()
ginger qz [] g = fred $ foldr GIVEN (PROVE g) qz
ginger qz ((ty, (l, r)) : qs) g =
  flip (cope (equal ty (l, r)))
  (\ _ -> ginger qz qs g)
  $ \ _ -> do
    ty <- norm ty
    l' <- hnf l
    r' <- hnf r
    case (ty, l', r') of
      (Prop, _ , _) -> ginger (qz :< (l :-> r) :< (r :-> l)) qs g
      (TC d ss, TC c rs, TC e ts)
        | c /= e -> flip (cope (isDataType d)) return $ \ _ -> dull
        | otherwise -> do
          tel <- constructor PAT ty c
          plan <- prepareSubQs tel rs ts
          ginger qz (glom [] plan ++ qs) g
      _ -> dull
  where
  dull = norm ty >>= \ ty -> ginger (qz :< TC "=" [ty, l, r]) qs g
  glom m [] = []
  glom m (((x, s), (a, b)) : plan) =
    (stan m s, (a, b)) : glom ((x, a) : m) plan


pout :: LayKind -> Make Anno TmR -> AM (Odd String [LexL])
pout k p@(Make mk g m (s, n) ps (h, b)) = let k' = scavenge b in case s of
  Keep -> do
    blk <- psout k' ps
    return $ (rfold lout (h `tense` n) . jank m . whereFormat b ps
             $ format k' blk)
             :-/ Stop
  Need -> do
    g <- ppTmR AllOK g
    blk <- psout k' ps
    return $ ((show mk ++) . (" " ++) . (g ++) . (" ?" ++) . whereFormat b ps
             $ format k' blk)
             :-/ Stop
  Junk e -> do
    e <- ppGripe e
    return $
      ("{- " ++ e) :-/ [(Ret, (0,0), "\n")] :-\
      (rfold lout h . rfold lout b $ "") :-/ [(Ret, (0,0), "\n")] :-\
      "-}" :-/ Stop
 where
   jank (Stub False) = (" ?" ++)
   jank (Tested False) = ("ed" ++)
   jank _ = id
   kws = [done mk b | b <- [False, True]]
   ((Key, p, s) : ls) `tense` n | elem s kws =
     (Key, p, done mk n) : ls
   (l : ls) `prove` n = l : (ls `prove` n)
   [] `prove` n = [] -- should never happen
   
   psout :: LayKind -> Bloc (SubMake Anno TmR) -> AM (Bloc String)
   psout k (g :-/ Stop) = return $ g :-/ Stop
   psout k (g :-/ SubPGuff [] :-\ h :-/ r) = psout k ((g ++ h) :-/ r)
   psout k (g :-/ p :-\ gpo) =
     (g :-/) <$> (ocato <$> subpout k p <*> psout k gpo)

   subpout :: LayKind -> SubMake Anno TmR -> AM (Odd String [LexL])
   subpout _ (SubPGuff ls)
     | all gappy ls = return $ rfold lout ls "" :-/ Stop
     | otherwise = return $ ("{- " ++ rfold lout ls " -}") :-/ Stop
   subpout _ ((srg, _) ::- Make m _ _ (Junk e, _) _ (h, b)) = do
     e <- ppGripe e
     return $
       ("{- " ++ e) :-/ [] :-\
       (rfold lout srg . rfold lout h . rfold lout b $ "") :-/ [] :-\
       "-}" :-/ Stop
   subpout k ((srg, (ds, gs)) ::- p) = do
     doorStop
     for ds $ \ (nom, u) -> push $ Bind (nom, Hide Prop) (User u) -- nasty
     z <- fish gs (pout k p) >>= \case
        p :-/ b -> (:-/ b) <$>
          ((if null srg then givs gs else pure $ rfold lout srg) <*> pure p)
     doorStep
     return z
    where
     fish [] p = p
     fish (Given h : gs) p = case my h of
       Nothing -> fish gs p
       Just h -> h |- fish gs p
     givs :: [Given TmR] -> AM (String -> String)
     givs gs = traverse wallop gs >>= \case
       [] -> return id
       g : gs -> return $ 
         ("given " ++) . (g ++) . rfold comma gs (" " ++)
       where
         wallop :: Given TmR -> AM String
         wallop (Given g) = ppTmR AllOK g
         comma s f = (", " ++) . (s ++) . f
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


noDuplicate :: Tm -> Con -> AM ()
noDuplicate ty con = cope (constructor EXP ty con)
  (\ _ -> return ())
  (\ _ -> gripe $ Duplication Prop con)

chkProp :: Appl -> Bloc RawIntro -> AM ()
chkProp (ls, (t, _, rel) :$$ as) intros | elem t [Uid, Sym]  = do
  noDuplicate Prop rel
  doorStop
  tel <- elabTel as
  pushOutDoor $ ("Prop", []) ::> (rel, tel)
  (rus, cxs) <- fold <$> traverse (chkIntro tel) intros
  guard $ nodup rus
  mapM_ pushOutDoor cxs
  doorStep
  return ()
 where
  chkIntro :: Tel -> RawIntro -> AM ([String], [CxE])
  chkIntro tel (RawIntro aps rp prems) = do
    doorStop
    push ImplicitQuantifier
    (ht, _) <- elabVec EXP rel tel aps
    (hp, sb0) <- patify ht
    (ru, as) <- case rp of
      (_, (t, _, ru) :$$ as) | elem t [Uid, Sym] -> return (ru, as)
      _ -> gripe FAIL
    return ()
    (vs, sb1) <- bindParam as
    let sb = sb0 ++ sb1
    guard $ nodup (map fst sb)
    pop $ \case {ImplicitQuantifier -> True; _ -> False}
    ps <- traverse chkPrem prems
    lox <- doorStep
    tel <- telify vs lox
    let (tel', ps') = rfold e4p sb (tel, toList ps)
    let byr = ByRule True $ (hp, (ru, tel')) :<= ps'
    return ([ru], [byr])
  chkPrem :: ([Appl], Appl) -> AM Subgoal
  chkPrem (hs, g) =
    rfold GIVEN <$> traverse (elabTm EXP Prop) hs <*> (PROVE <$> elabTm EXP Prop g)
chkProp _ intros = gripe FAIL

patify :: Tm -> AM (Pat, [(Nom, Syn)])
patify (TC c ts) = do
  (ts, sb) <- go ts
  return (PC c ts, sb)
 where
  go [] = return ([], [])
  go (t : ts) = do
    (t,  sb0) <- patify t
    (ts, sb1) <- go ts
    if null (intersect (map fst sb0) (map fst sb1))
      then return (t : ts, sb0 ++ sb1)
      else gripe FAIL
patify (TE (TP (xp, Hide ty))) = do
  User x <- nomBKind xp
  return (PM x mempty, [(xp, TM x [] ::: ty)])
patify _ = gripe FAIL

chkData :: Appl -> [Appl] -> AM ()
chkData (_, (t, _, tcon) :$$ as) vcons | elem t [Uid, Sym] = do
  noDuplicate Type tcon
  doorStop
  doorStop
  (vs, _) <- bindParam as
  fake <- gamma >>= (`fakeTel` Pr [])
  push $ ("Type", []) ::> (tcon, fake)
  cts <- traverse chkCon vcons
  guard $ nodup (map fst cts)
  lox <- doorStep
  real <- telify vs lox
  push $ ("Type", []) ::> (tcon , real)
  (ps, sb) <- mkPatsSubs 0 lox
  for cts $ \ (c, tel) ->
    push $ (tcon, ps) ::> (c, rfold e4p sb tel)
  ctors <- doorStep
  push $ Data tcon (B0 <>< ctors)
  return ()
 where
  fakeTel :: Context -> Tel -> AM Tel
  fakeTel B0 tel = return tel -- not gonna happen because...
  fakeTel (ga :< DoorStop) tel = return tel -- ...this prevents it
  fakeTel (ga :< Bind (_, Hide ty) (User x)) tel =
    fakeTel ga ((x, ty) :*: tel)
  fakeTel (ga :< _) tel = fakeTel ga tel
  chkCon :: Appl -> AM (String, Tel)
  chkCon (_, (t, _, vcon) :$$ as) | elem t [Uid, Sym] = do
    vtel <- elabTel as
    return (vcon, vtel)
  chkCon _ = gripe FAIL
  mkPatsSubs :: Int -> [CxE] -> AM ([Pat], [(Nom, Syn)])
  mkPatsSubs _ [] = return ([], [])
  mkPatsSubs i (Bind (xp, Hide ty) bk : lox) = case bk of
    Hole -> let x = '%' : show i in
      ((PM x mempty :) *** ((xp, TM x [] ::: ty) :)) <$> mkPatsSubs (i + 1) lox
    Defn t ->
      (id *** ((xp, t ::: ty) :)) <$> mkPatsSubs i lox
    User x ->
       ((PM x mempty :) *** ((xp, TM x [] ::: ty) :)) <$> mkPatsSubs (i + 1) lox
  mkPatsSubs i (_ : lox) = mkPatsSubs i lox
chkData _ _ = gripe FAIL

chkSig :: Appl -> Appl -> AM ()
chkSig la@(_, (t, _, f@(c : _)) :$$ as) rty
  | t == Lid || (t == Sym && c /= ':')
  = do
  -- cope (what's f) (\ gr -> return ()) (\ _ -> gripe $ AlreadyDeclared f)
  doorStop
  push ImplicitQuantifier
  xts <- placeHolders as
  rty <- elabTm EXP Type rty
  pop $ \case {ImplicitQuantifier -> True; _ -> False}
  lox <- doorStep
  sch <- schemify (map fst xts) lox rty
  fn <- fresh f
  push $ Declare f fn sch
  return ()
  | otherwise = gripe $ BadFName f

chkTest :: Appl -> Maybe Appl -> AM String
chkTest (ls, (_,_,f) :$$ as) mv = do
  (e, sy) <- elabSyn EXP f as
  case mv of
    Just t@(rs, _) -> do
      v <- elabTm EXP sy t
      b <- cope (equal sy (TE e, v)) (\ _ -> return False) (\ _ -> return True)
      if b
        then return . ("tested " ++) . rfold lout ls . (" = " ++) . rfold lout rs $ ""
        else do
          n <- norm (TE e)
          r <- ppTm AllOK n
          return . ("tested " ++) . rfold lout ls . (" = " ++) . (r ++) .
            ("{- not " ++) . rfold lout rs $ " -}"
    Nothing -> do
      v <- norm (TE e)
      r <- ppTm AllOK v
      return . ("tested " ++) . rfold lout ls . (" = " ++) $ r


discharge :: [CxE] -> Tm -> Tm
discharge zs t = go [] zs t where
  go sg [] t = rfold e4p sg t
  go sg (Bind (nom, Hide ty) k : zs) t = case k of
    Defn s -> go ((nom, rfold e4p sg (s ::: ty)) : sg) zs t
    _      -> go ((nom, TP (nom, Hide (rfold e4p sg ty))) : sg) zs t
  go sg (_ : zs) t = go sg zs t

askRawDecl :: (RawDecl, [LexL]) -> AM String
askRawDecl (RawProof (Make Prf gr mr () ps src), ls) = id <$
  doorStop <*>
  cope (do
      g <- impQElabTm Prop gr 
      gt <- mayhem $ my g
      de <- doorStep
      let claim = discharge de gt
      doorStop
      traverse push de
      prf <- chkProof g mr ps src
      p <- bifoldMap id (($ "") . rfold lout) <$> pout (Denty 1) prf
      let nailed = case annotation prf of
            (Keep, True) -> True
            _ -> False
      pushOutDoor . Hyp nailed $ claim
      return p)
    (\ gr -> do
      e <- ppGripe gr
      return $ "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}")
    return
  <* doorStep
askRawDecl (RawProof (Make Def gr@(_, (_, _, f) :$$ as) mr () ps src), ls) = do
  doorStop
  (b, s) <- cope (do
      push (Defined f)
      True <- tracy ("pushed Defined " ++ f) $ return True
      Left (fn, sch) <- what's f
      pop $ \case
        Defined g | f == g -> True
        _ -> False
      True <- tracy ("popped Defined " ++ f) $ return True
      p <- proglify fn (f, sch)
      p <- dubStep p f as
      True <- tracy (show p) $ return True
      ((True,) . bifoldMap id (($ "") . rfold lout)) <$> 
        (chkProg p gr mr ps src >>= pout (Denty 1))
      )
     (\ gr -> do
       e <- ppGripe gr
       return (False, "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}"))
     return
  doorStep
  if b then push (Defined f) else return ()
  return s
askRawDecl (RawProp tmpl intros, ls) = cope (chkProp tmpl intros)
  (\ gr -> do
    e <- ppGripe gr
    return $ "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}")
  (\ _ -> return $ rfold lout ls "")
askRawDecl (RawData tcon vcons, ls) = cope (chkData tcon vcons)
  (\ gr -> do
    e <- ppGripe gr
    return $ "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}")
  (\ _ -> return $ rfold lout ls "")
askRawDecl (RawSig la ra, ls) =
  cope (chkSig la ra)
  (\ gr -> do
    e <- ppGripe gr
    return $ "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}")
  (\ _ -> return $ rfold lout ls "")
askRawDecl (RawTest e mv, ls) =
  cope (chkTest e mv)
  (\ gr -> do
    e <- ppGripe gr
    return $ "{- " ++ e ++ "\n" ++ rfold lout ls "\n-}")
  return
askRawDecl (RawSewage, []) = return ""
askRawDecl (RawSewage, ls) = return $ "{- don't ask\n" ++ rfold lout ls "\n-}"
askRawDecl (_, ls) = return $ rfold lout ls ""

filth :: String -> String
filth s = case runAM go () initAskState of
  Left e -> "OH NO! " ++ show e
  Right (s, _) -> s
 where
  go :: AM String
  go = do
    ftab <- getFixities
    bifoldMap (($ "") . rfold lout) id <$> traverse askRawDecl (snd $ raw ftab s)

ordure :: String -> String
ordure s = case runAM go () initAskState of
  Left e -> "OH NO! " ++ show e
  Right (s, as) -> s ++ "\n-------------------------\n" ++ show as
 where
  go :: AM String
  go = do
    ft <- getFixities
    bifoldMap (($ "") . rfold lout) id <$> traverse askRawDecl (snd $ raw ft s)

initAskState :: AskState
initAskState = AskState
  { context  = myContext
  , root     = (B0, 0)
  , fixities = myFixities
  }

filthier :: AskState -> String -> (String, AskState)
filthier as s = case runAM go () as of
  Left e -> ("OH NO! " ++ show e, as)
  Right r -> r
 where
  go :: AM String
  go = do
    fi <- getFixities
    let (fo, b) = raw fi s
    setFixities fo
    bifoldMap (($ "") . rfold lout) id <$> traverse askRawDecl b

foo = unlines
  [ "data List x = Empty | x : List x"
  , "(++) :: List x -> List x -> List x"
  , "define xs ++ ys inductively xs where"
  , "  define xs ++ ys from xs where"
  , "    define Empty ++ ys = ys"
  , "    define (x : xs') ++ ys = x : (xs' ++ ys)"
  , "prove xs ++ Empty = xs inductively xs where"
  , "  prove xs ++ Empty = xs from xs where"
  , "    given xs = x : xs' prove (x : xs') ++ Empty = x : xs' tested"
  ]

goo = unlines
  [ "data Tree = Leaf | Node Tree Tree"
  , "mirror :: Tree -> Tree"
  , "define mirror t inductively t where"
  , "  define mirror t from t where"
  , "    define mirror Leaf = Leaf"
  , "    define mirror (Node l r) = Node (mirror r) (mirror l)"
  , "prove mirror (mirror t) = t inductively t where"
  , "  prove mirror (mirror t) = t from t where"
  , "    given t = Node l r prove mirror (mirror (Node l r)) = Node l r tested"
  ]

hoo = unlines
  [ "data List x = Empty | x : List x"
  , "(++) :: List x -> List x -> List x"
  , "define xs ++ ys inductively xs where"
  , "  define xs ++ ys from xs where"
  , "    define Empty ++ ys = ys"
  , "    define (x : xs') ++ ys = x : (xs' ++ ys)"
  , "prove (xs ++ ys) ++ zs = xs ++ (ys ++ zs) inductively xs where"
  , "  prove (xs ++ ys) ++ zs = xs ++ (ys ++ zs) from xs where"
  , "    given xs = x : xs' prove ((x : xs') ++ ys) ++ zs = (x : xs') ++ (ys ++ zs) tested"
  ]

ioo = unlines
  [ "data N = Z | S N"
  , "(+) :: N -> N -> N"
  , "defined x + y inductively x where"
  , "  defined x + y from x where"
  , "    defined Z + y = y"
  , "    defined S x + y = S (x + y)"
  , "prove (x + y) + z = x + (y + z) inductively x where"
  , "  prove (x + y) + z = x + (y + z) from x where"
  , "    given x = S x' prove (S x' + y) + z = S x' + (y + z)"
  , "      tested"
  ]