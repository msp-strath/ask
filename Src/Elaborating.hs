-----------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Elaborating                                  ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    PatternSynonyms
  , TupleSections
  , LambdaCase
#-}

module Ask.Src.Elaborating where

import qualified Data.Map as M
import Control.Arrow ((***))
import Data.Monoid
import Control.Monad.Writer
import Data.Traversable
import Debug.Trace

import Ask.Src.Bwd
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
    ElabSyn a -> elabSyn a
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
topSubMake ((_, gs) ::- Make k g m a sps src) = case k of
  Def -> return $ ElabGripe Mardiness -- for now
  Prf -> do
    push ImplicitForall
    traverse elabGiven gs
    goal <- chkElab "G" Prop g
    return $ ElabGripe Mardiness

elabGiven :: Given Appl -> AM ()
elabGiven (Given h) = do
  e <- chkElab "H" Prop h
  hyp <- chkTE Prop e
  push (Hyp hyp)



------------------------------------------------------------------------------
--  Terms
------------------------------------------------------------------------------

chkElab :: String -> Ty -> Appl -> AM Syn
chkElab x ty a = pushElab x (fst a) ty (ElabChk ty a)

elabChk :: Ty -> Appl -> AM Elab
elabChk trg a@(_, (_, _, f) :$$ _) = do
  trg <- chkHnf (Type, trg)
  anyCon f >>= \case
    [] -> do
      (e, src) <- synElab "e" a
      demand a $ Sub src trg
      return $ ElabDone e
    -- [(d, tel)] -> 
    dts -> case trg of
      TC d ss -> do
        tel <- conTel wangle (demand a) (d, ss) f
        argsElab "a" (f, tel) a trg
      TE e -> return $ ElabStuk (Canon e) (ElabChk (TE e) a)
 where
  wangle e (d, ss) c = do
    tel <- conTel wangle (demand a) (d, ss) c
    ts <- go tel
    demand a (Q (TC d ss) (TE e) (TC c ts))
    return ts
  go (Re _) = return []
  go (Sg _ s b) = do
    t <- hole "x" s
    (TE t :) <$> go (b // t)
  go (Pr p t) = id <$ demand a p <*> go t
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
      e <- chkElab z s a
      t <- chkTE s e
      (t :) <$> go (b // e) as
  go (Pr p t) as = id <$ demand src p <*> go t as
  go _ _ = gripe Mardiness

cellType :: Ty
cellType = Sigma Type (L (TE (TV 0)))

synElab :: String -> Appl -> AM (Syn, Ty)
synElab x a = do
  r <- pushElab x (fst a) cellType (ElabSyn a)
  hnfSyn (r :$ Snd)

elabSyn :: Appl -> AM Elab
elabSyn a@(_, (_, _, f) :$$ as) = seek (i'm f) >>= \case
  _ :< The l -> let xd = myDecl l in
    elabSpine (TP xd, tel xd) a
  B0 -> do
    xd <- invent f
    elabSpine (TP xd, tel xd) a
 where
  i'm f (The l) = case who (myDecl l) of
    Just (g, _) -> f == g
    _ -> False
  i'm f _ = False
  tel d = case who d of
    Just (_, t) -> t
    Nothing     -> Re (typ d)
  
elabSpine :: (Syn, Tel Ty) -> Appl -> AM Elab
elabSpine et y@(_, _ :$$ as) = go et as where
  go (e, tel) [] = do
    ty <- dumpTel y tel
    return . ElabDone $ Pair ty (TE e) ::: cellType
  go (e, Impl s b) as = do
    x <- hole "x" s
    go (e :$ TE x, b // x) as
  go (e, Pr p t) as = id <$ demand y p <*> go (e, t) as
  go (e, Expl s b) (a : as) = do
    f <- chkElab "x" s a
    v <- chkTE s f
    go (e :$ v, b // f) as
  go (e, Re ty) as = do
    (dom, ran) <- mkFun y ty
    go (e, Expl dom (K ran)) as

dumpTel :: Appl -> Tel Ty -> AM Ty
dumpTel _ (Re ty) = return ty
dumpTel y (Expl s (K tel)) = (s :->) <$> dumpTel y tel
dumpTel y _ = gripe $ Underapplied y

mkFun :: Appl -> Ty -> AM (Ty, Ty)
mkFun _ (dom :-> ran) = return (dom, ran)
mkFun y ty = do
  dom <- TE <$> hole "dom" Type
  ran <- TE <$> hole "ran" Type
  demand y $ Q Type ty (dom :-> ran)
  return (dom, ran)

invent :: String -> AM Decl
invent x = AM $ \ _ lz -> go lz where
  go B0 = Left (Scope x)
  go (lz :< l) = case yo (nom (myDecl l), myNext l) (myPast l) of
    Just (d, ez) -> Right (d, lz :< l {myPast = ez, myNext = myNext l + 2})
    Nothing -> (id *** (:< l)) <$> go lz
  yo _ B0 = Nothing
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



------------------------------------------------------------------------------
--  Demanding
------------------------------------------------------------------------------

demand :: Appl -> Pr -> AM ()
demand z (Sub s t) = do
  s <- chkHnf (Type, s)
  t <- chkHnf (Type, t)
  subtype s t >>= \case
    True -> return ()
    False -> case (s, t) of
      (s0 :-> t0, t) -> do
        (s1, t1) <- mkFun z t
        demand z (Sub s1 s0)
        demand z (Sub t0 t1)
      (s, s1 :-> t1) -> do
        (s0, t0) <- mkFun z s
        demand z (Sub s1 s0)
        demand z (Sub t0 t1)
      _ -> demand z (Q Type s t)
demand z p@(Q ty s t) = do
  ty <- chkHnf (Type, ty)
  s <- chkHnf (ty, s)
  t <- chkHnf (ty, t)
  equal ty (s, t) >>= \case
    True -> return ()
    False -> case (s, t) of
      (TE (TP x), _) | orange x -> push $ Solve z x (t ::: ty)
      (_, TE (TP x)) | orange x -> push $ Solve z x (s ::: ty)
      (TC b ss, TC c ts)
        | b /= c ->
          gripe $ UnificationError z s t ty
        | otherwise -> case ty of
            TC d rs -> do
              tel <- conTell (d, rs) c
              (ss', _) <- runTell tel ss
              (ts', _) <- runTell tel ts
              unifies ss' ts' `terror` UnificationError z s t ty
            _ -> gripe Mardiness
      _ -> push $ Fred z (Q ty s t)
 where
  unifies [] [] = return ()
  unifies ((s, a) : xs) ((t, b) : ys) = do
    demand z (Q t (TE (TE (a ::: s) ::: t)) b)
    unifies xs ys
  unifies _ _ = gripe FAIL
demand a _ = gripe Mardiness


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
            (_ , Any False) -> if visitMe (wot d)
              then do
                topon $ l'
                  { myProb = update nu (myProb l')
                  , myPast = B0
                  , myFutu = myPast l' <>> myFutu l'
                  }
                ambulando nu
              else do
                push (The l')
                ambulando nu
            (d, Any True) -> if visitMe (wot d)
              then do
                prep . Pend $ nom d %= d
                topon $ l'
                  { myDecl = d
                  , myProb = update nu (myProb l')
                  , myPast = B0
                  , myFutu = myPast l' <>> myFutu l'
                  }
                ambulando nu
              else do
                push (The l' {myDecl = d})
                ambulando $ nu >< (nom d %= d)
        Pend ol -> do
          topon $ l {myFutu = es}
          ambulando (nu <> ol)
        Fred z pr -> do
          topon $ l {myFutu = es}
          case runWriter (mangle (newsMang nu) pr) of
            (pr, Any False) -> do
              push $ Fred z pr
              ambulando nu
            (pr, Any True) -> do
              push $ Pend mempty
              prep $ Pend nu
              demand z (update nu pr)
              nu <- unPend
              ambulando nu
        Solve z x e -> do
          prep $ Pend nu
          aha x [] e
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
    prep $ The l
    aha x ds e


------------------------------------------------------------------------------
--  Experimental Stuff
------------------------------------------------------------------------------

myTest :: String
myTest = "given a & b prove b & a ?"

foo = runAM (ambulando mempty)
        mySetup
        (B0 :< startLayer myPreamble (raw myFixities myTest))