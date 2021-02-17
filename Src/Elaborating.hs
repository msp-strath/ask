------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Elaborating                                  ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    PatternSynonyms
  , TupleSections
  , LambdaCase
  , PatternGuards
#-}

module Ask.Src.Elaborating where

import qualified Data.Map as M
import Control.Arrow ((***))
import Data.Monoid
import Control.Monad.Writer
import Data.Traversable
import Debug.Trace

import Ask.Src.Bwd
import Ask.Src.OddEven
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Context
import Ask.Src.Computing
import Ask.Src.HardwiredRules

trunk = trace

------------------------------------------------------------------------------
--  Elaboration
------------------------------------------------------------------------------

elaborate {- dalek voice -} :: AM Elab
elaborate = cope go (return . ElabGripe) return
  where
  go = problem >>= \case
    ElabDecl r -> case r of
      RawProof p -> topSubMake p
      RawSewage -> gripe SyntaxError
      _ -> return $ ElabDecl r
    ElabChk ty a' -> elabChk ty a'
    ElabPrfFrom a p goal -> elabPrfFrom a p goal
    ElabPrfCase goal ts r -> elabPrfCase goal ts r
    ElabSyn a -> elabSyn a
    ElabSub s -> elabSub s
    ElabFred z p -> elabFred z p
    p -> return p


pushElab :: String -> [LexL] -> Ty -> Elab -> AM Syn
pushElab x txt ty p = do
  x <- fresh x
  let xd = Decl
        { nom = x
        , typ = ty
        , wot = Orange
        , who = Nothing
        }
  let xl = dummyLayer
        { myDecl = xd
        , myText = txt
        , myProb = p
        , myStat = New
        }
  topon xl
  elaborate >>= \case
    ElabDone e -> do
      l <- topov
      let xd' = xd { wot = green e }
      push . The $ l { myProb = NoElab, myDecl = xd' }
      return e
    p -> do
      l <- topov
      push . The $ l { myProb = p }
      return (TP xd)


------------------------------------------------------------------------------
--  Proof/Program elaboration
------------------------------------------------------------------------------

topSubMake :: SubMake () Appl -> AM Elab
topSubMake ((_, gs) ::- Make k g m () sps (_, sb)) = case k of
  Def -> return $ ElabGripe Mardiness -- for now
  Prf -> do
    push ImplicitForall
    traverse elabGiven gs
    goal <- chkElab "G" Prop g
    elabPrf goal m sps sb

elabPrf :: Pr -> Method Appl -> Bloc (SubMake () Appl) -> [LexL] -> AM Elab
elabPrf goal m sps sb = do
  push BeginWhere
  traverse subElab sps
  push EndWhere
  case m of
    From p -> do
      cut <- chkElab "C" Prop p
      elabPrfFrom p cut goal
    _ -> return $ ElabGripe Mardiness

elabPrfFrom :: Appl -> Pr -> Pr -> AM Elab
elabPrfFrom p cut goal = chkHnf (Prop, cut) >>= \case
  TC c ss -> do
    fred (Just p) $ TC c ss
    (_ :- _, rs) <- cope (connective c)
      (\ _ -> gripe (FromNeedsConnective p))
      return
    case rs of
      [_ :- tel] -> cope (do
          (_, Re (Cons sg Nil)) <- runTell tel ss
          flip sg
          )
        (\ _ -> do
          traverse (prfCase goal ss) [tel | _ :- tel <- rs]
          return $ ElabDone (TRUE ::: Prop))
        return
      _ -> do
        traverse (prfCase goal ss) [tel | _ :- tel <- rs]
        return $ ElabDone (TRUE ::: Prop)
  TE e -> return . ElabStuk (Canon e) $ ElabPrfFrom p (TE e) goal
  _ -> return $ ElabGripe Mardiness
  where
    flip (GIVEN h g) = do
      fred Nothing h
      flip g
    flip (PROVE g) = do
      prfCase goal [] (Re . Re $ Cons (PROVE g) Nil)
      return $ ElabDone (TRUE ::: Prop)
    flip _ = gripe Mardiness

prfCase :: Pr -> [Tm] -> Tel (Tel [Subgoal]) -> AM ()
prfCase goal ss tel = () <$ pushElab "g" [] Prop (ElabPrfCase goal ss tel)

elabPrfCase :: Pr -> [Tm] -> Tel (Tel [Subgoal]) -> AM Elab
elabPrfCase goal ss tel = do
  (_, tel) <- runTel wangle ginger tel ss
  (ts, sg) <- spose tel
  go sg
 where
  wangle e (d, ss) c = do
    tel <- conTell (d, ss) c
    (ts, _) <- spose tel
    push . Hyp $ Q (TC d ss) (TE e) (TC c ts)
    return ts
  go (Cons g gs) = do
    h <- flop g
    push $ Hyp h
    go gs
  go Nil = elabFred Nothing goal
  flop (GIVEN h g) = (h :->) <$> flop g
  flop (PROVE g) = return g
  flop _ = gripe Mardiness

spose :: Tel x -> AM ([Tm], Chk)
spose (Re x) = return ([], x)
spose (Pr h t) = do
  ginger h
  spose t
spose (Sg _ s b) = do
  yd <- purple "x" s
  (ts, x) <- spose (b // TP yd)
  return (TE (TP yd) : ts, x)
spose _ = gripe Mardiness

elabGiven :: Given Appl -> AM ()
elabGiven (Given h) = do
  hyp <- chkElab "H" Prop h
  push (Hyp hyp)

subElab :: SubMake () Appl -> AM Syn
subElab s@(SubPGuff ls) = pushElab
  "guff"
  ls
  Prop
  (ElabGripe SyntaxError)
subElab s@((ls, _) ::- m)  = pushElab
  "sub"
  (ls ++ fst (source m) ++ snd (source m))
  Prop
  (ElabSub s)

elabSub :: SubMake () Appl -> AM Elab
elabSub s@((_, gs) ::- m) = return $ ElabSub s
  -- not for ever


------------------------------------------------------------------------------
--  Terms
------------------------------------------------------------------------------

chkElab :: String -> Ty -> Appl -> AM Chk
chkElab x trg a = do
  e <- pushElab x (fst a) trg (ElabChk trg a)
  (e, src) <- dnfSyn e
  ship e src trg

elabChk :: Ty -> Appl -> AM Elab
elabChk trg a@(_, (_, _, f) :$$ as) = do
  trg <- chkHnf (Type, trg)
  anyCon f >>= \case
    [] -> case as of
      [] -> seek (i'm f) >>= \case
        _ :< The l -> let xd = myDecl l in do
          fred (Just a) $ Sub (typ xd) trg
          return $ ElabDone (TP xd)
        B0 -> do
          xd <- invent (Just trg) f a
          return $ ElabDone (TP xd)
      _ -> do
        (e, src) <- synElab "e" a
        fred (Just a) $ Sub src trg
        return $ ElabDone e
    -- [(d, tel)] -> 
    dts -> case trg of
      TC d ss -> do
        tel <- conTel wangle (fred (Just a)) (d, ss) f
        argsElab "a" (f, tel) a trg
      TE e -> return $ ElabStuk (Canon e) (ElabChk (TE e) a)
 where
  wangle e (d, ss) c = do
    tel <- conTel wangle (fred (Just a)) (d, ss) c
    ts <- go tel
    fred (Just a) (Q (TC d ss) (TE e) (TC c ts))
    return ts
  go (Re _) = return []
  go (Sg _ s b) = do
    t <- hole "x" s
    (TE t :) <$> go (b // t)
  go (Pr p t) = id <$ fred (Just a) p <*> go t
  go _ = gripe Mardiness

argsElab :: String -> (Con, Tel ()) -> Appl -> Ty -> AM Elab
argsElab z (c, tel) src@(_, _ :$$ as) trg = do
  ts <- go tel as
  return $ ElabDone (TC c ts ::: trg)
 where
  err = Arity (c, tel) as
  go :: Tel () -> [Appl] -> AM [Tm]
  go (Re _) as = if null as
    then return []
    else gripe err
  go (Impl s b) as = do
    t <- hole z s
    (TE t :) <$> go (b // t) as
  go (Expl s b) as = case as of
    [] -> gripe err
    (a : as) -> do
      t <- chkElab z s a
      (t :) <$> go (b // (t ::: s)) as
  go (Pr p t) as = id <$ fred (Just src) p <*> go t as
  go _ _ = gripe Mardiness

cellType :: Ty
cellType = Sigma Type (L (TE (TV 0)))

synElab :: String -> Appl -> AM (Syn, Ty)
synElab x a = do
  r <- pushElab x (fst a) cellType (ElabSyn a)
  hnfSyn (r :$ Snd)

elabSyn :: Appl -> AM Elab
elabSyn a@(_, (_, _, "::") :$$ [tm, ty]) = do
  ty <- chkElab "T" Type ty
  tm <- chkElab "t" ty tm
  return . ElabDone $ tm ::: ty
elabSyn a@(_, (_, _, f) :$$ as) = seek (i'm f) >>= \case
  _ :< The l -> let xd = myDecl l in
    elabSpine (TP xd, tel xd) a
  B0 -> do
    xd <- invent Nothing f a
    elabSpine (TP xd, tel xd) a
 where
  tel d = case who d of
    Just (_, t) -> t
    Nothing     -> Re (typ d)

i'm :: String -> Entry -> Bool
i'm f (The l) = case who (myDecl l) of
  Just (g, _) -> f == g
  _ -> False
i'm f _ = False


elabSpine :: (Syn, Tel Ty) -> Appl -> AM Elab
elabSpine et y@(_, _ :$$ as) = go et as where
  go (e, tel) [] = do
    ty <- dumpTel y tel
    return . ElabDone $ Pair ty (TE e) ::: cellType
  go (e, Impl s b) as = do
    x <- hole "x" s
    go (e :$ TE x, b // x) as
  go (e, Pr p t) as = id <$ fred (Just y) p <*> go (e, t) as
  go (e, Expl s b) (a : as) = do
    v <- chkElab "x" s a
    go (e :$ v, b // (v ::: s)) as
  go (e, Re ty) as = do
    (dom, ran) <- mkFun (Just y) ty
    go (e, Expl dom (K ran)) as

dumpTel :: Appl -> Tel Ty -> AM Ty
dumpTel _ (Re ty) = return ty
dumpTel y (Expl s (K tel)) = (s :->) <$> dumpTel y tel
dumpTel y _ = gripe $ Underapplied y

mkFun :: Maybe Appl -> Ty -> AM (Ty, Ty)
mkFun _ (dom :-> ran) = return (dom, ran)
mkFun y ty = do
  dom <- TE <$> hole "dom" Type
  ran <- TE <$> hole "ran" Type
  fred y $ Q Type ty (dom :-> ran)
  return (dom, ran)

invent :: Maybe Ty -> String -> Appl -> AM Decl
invent Nothing x a = AM $ \ _ lz -> go lz where
  go B0 = Left (Scope x)
  go (lz :< l) = case yo (nom (myDecl l), myNext l) (myPast l) of
    Just (d, ez) -> Right (d, lz :< l {myPast = ez, myNext = myNext l + 3})
    Nothing -> (id *** (:< l)) <$> go lz
  yo _ B0 = Nothing
  yo (n, i) (ez :< EndWhere) =
    Just (xd, ez :< The tl :< The xl :< EndWhere :< The fl)
    where
    td = Decl { nom = n ++ [(x ++ "Ty", i)]
              , typ = Type
              , wot = Orange
              , who = Nothing
              }
    tl = dummyLayer { myDecl = td }
    xd = Decl { nom = n ++ [(x, i + 1)]
              , typ = TE (TP td)
              , wot = Orange
              , who = Just (x, Re $ TE (TP td))
              }
    xl = dummyLayer { myDecl = xd, myProb = ElabStub }
    fd = Decl { nom = n ++ [(x ++ "def", i + 2)]
              , typ = Prop
              , wot = Orange
              , who = Nothing
              }
    fl = dummyLayer
      { myDecl = fd
      , myProb = ElabFred (Just a) (Defd (TE (TP td)) (TE (TP xd)))
      }
  yo (n, i) (ez :< ImplicitForall) =
    Just (xd, ez :< The tl :< The xl :< ImplicitForall)
    where
    td = Decl { nom = n ++ [(x ++ "Ty", i)]
              , typ = Type
              , wot = Orange
              , who = Nothing
              }
    tl = dummyLayer { myDecl = td }
    xd = Decl { nom = n ++ [(x, i + 1)]
              , typ = TE (TP td)
              , wot = Purple
              , who = Just (x, Re $ TE (TP td))
              }
    xl = dummyLayer { myDecl = xd }
  yo ni (ez :< e) = (id *** (:< e)) <$> yo ni ez
invent (Just ty) x a = AM $ \ _ lz -> go lz where
  go B0 = Left (Scope x)
  go (lz :< l) = case yo (nom (myDecl l), myNext l) (myPast l) of
    Just (d, ez) -> Right (d, lz :< l {myPast = ez, myNext = myNext l + 2})
    Nothing -> (id *** (:< l)) <$> go lz
  yo _ B0 = Nothing
  yo (n, i) (ez :< EndWhere) =
    Just (xd, ez :< The xl :< EndWhere :< The fl)
    where
    xd = Decl { nom = n ++ [(x, i + 1)]
              , typ = ty
              , wot = Orange
              , who = Just (x, Re ty)
              }
    xl = dummyLayer { myDecl = xd, myProb = ElabStub }
    fd = Decl { nom = n ++ [(x ++ "def", i + 2)]
              , typ = Prop
              , wot = Orange
              , who = Nothing
              }
    fl = dummyLayer
      { myDecl = fd
      , myProb = ElabFred (Just a) (Defd ty (TE (TP xd)))
      }
  yo (n, i) (ez :< ImplicitForall) =
    Just (xd, ez :< The xl :< ImplicitForall)
    where
    xd = Decl { nom = n ++ [(x, i + 1)]
              , typ = ty
              , wot = Purple
              , who = Just (x, Re ty)
              }
    xl = dummyLayer { myDecl = xd }
  yo ni (ez :< e) = (id *** (:< e)) <$> yo ni ez


------------------------------------------------------------------------------
--  Ginger Rogers
------------------------------------------------------------------------------

ginger :: Pr -> AM ()
ginger h = push $ Hyp h   -- not for ever


------------------------------------------------------------------------------
--  Fred Astaire
------------------------------------------------------------------------------

fred :: Maybe Appl -> Pr -> AM ()
fred z p = () <$ pushElab "fred" [] Prop (ElabFred z p)

elabFred :: Maybe Appl -> Pr -> AM Elab
elabFred z (Sub s t) = do
    s <- chkHnf (Type, s)
    t <- chkHnf (Type, t)
    subtype s t >>= \case
      True -> return . ElabDone $ TRUE ::: Prop
      False -> case (s, t) of
        (s0 :-> t0, t) -> do
          (s1, t1) <- mkFun z t
          fred z (Sub s1 s0)
          fred z (Sub t0 t1)
          return . ElabDone $ TRUE ::: Prop
        (s, s1 :-> t1) -> do
          (s0, t0) <- mkFun z s
          fred z (Sub s1 s0)
          fred z (Sub t0 t1)
          return . ElabDone $ TRUE ::: Prop
        _ -> elabFred z (Q Type s t)
elabFred z p@(Q ty s t) = do
  ty <- chkHnf (Type, ty)
  s <- chkHnf (ty, s)
  t <- chkHnf (ty, t)
  equal ty (s, t) >>= \case
    True -> return . ElabDone $ TRUE ::: Prop
    False -> case (s, t) of
      (TE (TP x), _) | orange x -> do
        push $ Solve z x (t ::: ty)
        return . ElabDone $ TRUE ::: Prop
      (_, TE (TP x)) | orange x -> do
        push $ Solve z x (s ::: ty)
        return . ElabDone $ TRUE ::: Prop
      (TC b ss, TC c ts)
        | b /= c ->
          gripe $ UnificationError z s t ty
        | otherwise -> case ty of
            TC d rs -> do
              tel <- conTell (d, rs) c
              (ss', _) <- runTell tel ss
              (ts', _) <- runTell tel ts
              unifies ss' ts' `terror` UnificationError z s t ty
              return . ElabDone $ TRUE ::: Prop
            _ -> gripe Mardiness
      _ -> return $ ElabFred z p
 where
  unifies [] [] = return ()
  unifies ((s, a) : xs) ((t, b) : ys) = do
    fred z (Q t (TE (TE (a ::: s) ::: t)) b)
    unifies xs ys
  unifies _ _ = gripe FAIL
elabFred z p = return $ ElabFred z p


------------------------------------------------------------------------------
--  Solvitur Ambulando
------------------------------------------------------------------------------

ambulandone :: AM Bool
ambulandone = AM $ \ _ lz -> case lz of
  B0 :< l | null . myFutu $ l -> Right (True, lz)
  _ -> Right (False, lz)

unPend :: AM News
unPend = do
  l <- topov
  case nearest (\case {Pend nu -> Just nu; _ -> Nothing}) (myPast l) of
    Nothing -> gripe Mardiness
    Just (ez, nu, es) -> do
      topon  $ l {myPast = ez, myFutu = es}
      return nu

visitMe :: Colour -> Bool
visitMe Orange           = True
visitMe (Green False _)  = True
visitMe _                = False

visitStat :: Status -> Bool
visitStat Hot = True
visitStat New = True
visitStat _ = False

spruceUp :: Decl -> AM Decl
spruceUp d = do
  ty <- chkDnf (Type, typ d)
  wo <- case wot d of
    Green b e -> do
      (e, _) <- dnfSyn e
      return $ green e
    w -> return w
  return $ d { typ = ty, wot = wo }

ambulando :: News -> AM ()
ambulando nu = ambulandone >>= \case
  True -> return ()
  False -> do
    l <- topov
    case myFutu l of
      [] -> do
        topon $ l
        push $ Pend nu
        p <- elaborate
        ez <- topol (return . myPast)
        nu <- unPend
        topol (return . myFutu) >>= \case
          _ : _ -> do
            l <- topov
            topon $ l {myProb = p}
            ambulando nu
          [] -> do
            l <- topov
            case p of
              ElabDone e -> do
                let x = (myDecl l) {wot = green e}
                push (The $ l {myDecl = x, myProb = NoElab, myPast = ez})
                ambulando $ nu >< (nom x %= x)
              _ -> do
                push (The $ l {myProb = p})
                ambulando nu
      e : es -> case e of
        _ | trunk ("AMBULANDO: " ++ show e) False -> undefined
        The l' -> do
          topon $ l {myFutu = es}
          let d = myDecl l'
          case runWriter (mangle (newsMang nu) d) of
            (_ , Any False) -> if visitMe (wot d) || visitStat (myStat l')
              then do
                topon $ l'
                  { myProb = update nu (myProb l')
                  , myPast = B0
                  , myFutu = myPast l' <>> myFutu l'
                  , myStat = Old
                  }
                ambulando nu
              else do
                push (The l')
                ambulando nu
            (d, Any True) -> do
              d <- spruceUp d
              if visitMe (wot d) || visitStat (myStat l')
                then do
                  prep . Pend $ nom d %= d
                  topon $ l'
                    { myDecl = d
                    , myProb = update nu (myProb l')
                    , myPast = B0
                    , myFutu = myPast l' <>> myFutu l'
                    , myStat = Old
                    }
                  ambulando nu
                else do
                  push (The l' {myDecl = d})
                  ambulando $ nu >< (nom d %= d)
        Pend ol -> do
          topon $ l {myFutu = es}
          ambulando (nu <> ol)
        Solve z x e -> do
          topon $ l {myFutu = es}
          prep $ Pend nu
          aha x [] e
        Hyp h -> do
          h <- chkDnf (Prop, update nu h)
          topon $ l {myPast = myPast l :< Hyp h, myFutu = es}
          ambulando nu
        _ -> do
          topon $ l {myPast = myPast l :< e, myFutu = es}
          ambulando nu

aha :: Decl       -- known to be Orange
    -> [Decl]     -- the Orange crew we're moving out
    -> Syn        -- the term we're going to define the thing to be
    -> AM ()
aha x ds e = pop (const True) >>= \case
  Just (The l)
    | dep (myDecl l) (ds, e) -> let d = myDecl l in case wot d of
        Green _ f -> do
          prep (The l)
          aha x ((nom d \\ ds) // f) ((nom d \\ e) // f)
        Orange
          | x == d -> gripe FAIL
          | otherwise -> case myProb l of
              NoElab -> aha x (myDecl l : ds) e
              _ -> gripe FAIL
        _ -> gripe FAIL
    | x == myDecl l -> case myProb l of
        NoElab {- win! -} -> do
          let d = myDecl l
          let d' = d { wot = green e }
          for ds $ \ p -> push $ The (dummyLayer {myDecl = p})
          push . The $ l { myDecl = d' }
          ambulando $ nom d %= d'
        _ -> gripe FAIL
  Just z -> do
    prep z
    aha x ds e
  Nothing -> do
    l <- topov
    topox Mardiness
    prep . The $ l { myStat = Hot }
    aha x ds e


------------------------------------------------------------------------------
--  Experimental Stuff
------------------------------------------------------------------------------

myTest :: String
myTest = "given a -> b prove p from a -> b"

foo = runAM (ambulando mempty)
        mySetup
        (B0 :< startLayer myPreamble (raw myFixities myTest))