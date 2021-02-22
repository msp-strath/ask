------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Progging                                     ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    LambdaCase
#-}

module Ask.Src.Progging where

import Data.Char
import Data.List hiding ((\\))
import Control.Monad
import Data.Monoid
import Data.Traversable
import Control.Arrow ((***))

import Debug.Trace

import Ask.Src.Bwd
import Ask.Src.Hide
import Ask.Src.HalfZip
import Ask.Src.Tm
import Ask.Src.Context
import Ask.Src.Typing
import Ask.Src.Lexing
import Ask.Src.RawAsk

trade = const id


------------------------------------------------------------------------------
--  From Type Scheme to Programming Problem
------------------------------------------------------------------------------

proglify :: Nom -> (String, Sch) -> AM Proglem
proglify f (u, s) = go B0 B0 s where
  go de iz (as :>> t) = do
    ysxs <- traverse (\ (x, s) -> fresh x >>= \ y -> return (y, s, x)) as
    let m = [(x, TE (TP (y, Hide (stan m s)))) | (y, s, x) <- ysxs]
    return $ Proglem
      { localCx = de <>< [Bind xp (User x) | (x, TE (TP xp)) <- m]
      , fNom = f
      , uName = u
      , leftImpl = iz <>> []
      , leftSatu = [(tm, ty) | (_, tm@(TE (TP (_, Hide ty)))) <- m]
      , leftAppl = []
      , rightTy = stan m t
      }
  go de iz (Al a s) = do
    x <- fresh ""
    let xp = (x, Hide a)
    go (de :< Bind xp (User "")) (iz :< (TE (TP xp), a)) (s // TP xp)
  

------------------------------------------------------------------------------
--  get names from user
------------------------------------------------------------------------------

dubStep :: Proglem -> String -> [Appl] -> AM Proglem
dubStep p f as = do
  True <- trade ("DUBSTEP " ++ show p ++ "  " ++ show f ++ show as) $ return True
  doorStop
  push ImplicitQuantifier
  (e, ty) <- elabSyn f as
  lox <- doorStep
  z@(f, _, is, ss, as) <- mayhem $ fnarg e []
  True <- trade ("FNARG " ++ show z) $ return True
  guard $ f == fNom p
  p <- tro lox as (leftAppl p) p
  True <- trade (show p ++ "\nDUBBING") $ return True
  nx <- nub <$> ((++)
    <$> dubs lox (map fst $ leftSatu p) ss
    <*> dubs lox (map fst $ leftAppl p) as)
  True <- trade (show nx) $ return True
  guard $ length nx == length (nub (map snd nx))
  return $ p {localCx = fmap (redub nx) (localCx p)}
 where
  tro :: [CxE] -> [Tm] -> [(Tm, Tm)] -> Proglem -> AM Proglem
  tro lox [] [] p = return p
  tro lox (_ : as) (_ : la) p = tro lox as la p
  tro lox (TE (TP (yn, _)) : as) [] p = case [u | Bind (zn, _) (User u) <- lox , yn == zn] of
    [x] -> do
      True <- trade (show x ++ " tro " ++ show (rightTy p)) $ return True
      TC "->" [dom, ran] <- hnf (rightTy p)
      xn <- fresh x
      let xp = (xn, Hide dom)
      tro lox as [] $ p
        { localCx  = localCx p :< Bind xp (User x)
        , leftAppl = leftAppl p ++ [(TE (TP xp), dom)]
        , rightTy  = ran
        }
    _ -> gripe FAIL
  tro _ _ _ _ = gripe FAIL
  dubs :: [CxE] -> [Tm] -> [Tm] -> AM [(Nom, String)]
  dubs lox as bs | trade (show ("DUBS" ++ show as ++ show bs)) False = undefined
  dubs lox [] [] = return []
  dubs lox (TC c ts : ts') (TC d us : us')
    | c == d = dubs lox (ts ++ ts') (us ++ us')
    | otherwise = gripe FAIL
  dubs lox (TE (TP (xn, _)) : ts) (TE (TP (un, _)) : us) =
    case [u | Bind (yn, _) (User u) <- lox, yn == un] of
      [u] -> ((xn, u) :) <$> dubs lox ts us
      _   -> gripe FAIL
  dubs _ _ _ = gripe FAIL
  redub nx (Bind xp@(xn, _) (User y)) = case lookup xn nx of
    Just x -> Bind xp (User x)
    Nothing -> Bind xp (User (fuzz y))
  redub nx z = z
  fuzz "" = ".x"
  fuzz (c : cs) | isAlpha c = '.' : c : cs
  fuzz x = x


------------------------------------------------------------------------------
--  inductively
------------------------------------------------------------------------------

inductively :: Proglem -> [String] -> AM Proglem
inductively p@(Proglem de f u li ls la ty) xs = do
  True <- trade ("inductively " ++ show p) $ return True
  xs <- traverse (chkIsData de) xs
  non <- fresh "" -- make a nonce
  let nonp = (non, Hide Zone)
  let nont = TE (TP nonp)
  let size1 (xn, Hide s)
        | elem xn xs =  TC "$" [s, nont, TC "S" [TC "Z" []]]
        | otherwise = s
  let disTy [] ty = return ty
      disTy ((TE (TP xp), _) : la) t = (size1 xp :->) <$> disTy la t
      disTy _ _ = gripe FAIL
  aty <- disTy la ty
  qs <- for ls $ \case
    (TE (TP xp), _) -> case
      foldMap (\case {Bind yp (User y) | xp == yp -> [y]; _ -> []}) de of
      [x] -> return (xp, (x, size1 xp))
  let sa = [(fst xp, (TM x [] ::: rfold e4p sa s)) | (xp, (x, s)) <- qs]
  let disch [] = return $ [(x, rfold e4p sa s) | (_, (x, s)) <- qs] :>> aty
      disch ((TE (TP xp), _) : li) =
        (Al (size1 xp) . (fst xp \\)) <$> disch li
      disch _ = gripe FAIL
  sch <- disch li
  True <- trade (show "INDHYP " ++ show sch) $ return True
  let mark B0 = return $ ([], B0
        :< Bind (non, Hide Zone) (User "")
        :< Declare (uName p) (fNom p) sch)
      mark (ga :< Bind yp@(yn, Hide ty) (User y)) | elem yn xs = do
        ty <- hnf ty
        (sb, ga) <- mark ga
        let yp' = (yn, Hide (TC "$" [rfold e4p sb ty, nont, TC "Z" []]))
        return ((yn, TP yp') : sb, ga :< Bind yp' (User y))
      mark (ga :< z) = do
        (sb, ga) <- mark ga
        case z of
          Hyp h -> return (sb, ga :< Hyp (rfold e4p sb h))
          Bind (yn, Hide ty) k -> do
            let yp = (yn, Hide (rfold e4p sb ty))
            return ((yn, TP yp) : sb, ga :< Bind yp k)
          z -> return (sb, ga :< z) 
  (sb, de) <- mark de
  return $ Proglem de f u
    (rfold e4p sb li)
    (rfold e4p sb ls)
    (rfold e4p sb la)
    (rfold e4p sb ty)

isDataType :: Con -> AM ()
isDataType d = do
  ga <- gamma
  guard . getAny $ foldMap (Any . isda d) ga
 where
  isda d (Data e _) = d == e
  isda _ _ = False

chkIsData :: Context -> String -> AM Nom
chkIsData de x = case foldMap spot de of
  [(xn, Hide ty)] -> do
    ty@(TC d _) <- hnf ty
    isDataType d
    return xn
  _ -> gripe $ Scope x
  where
    spot (Bind xp (User y)) | y == x = [xp]
    spot _ = []


indPrf :: Tm -> [String] -> AM ()
indPrf g xs = do
  non <- fresh "" -- make a nonce
  let nonp = (non, Hide Zone)
  let nont = TE (TP nonp)
  ((ws, wg), (bs, bg)) <- qpr xs nont (([], g), ([], g))
  push $ Bind nonp (User "")
  traverse (\ (xp, u) -> push $ Bind xp (User u)) bs
  push $ Hyp wg
  demand $ PROVE bg
  ga <- gamma
  True <- trade ("INDPRF: " ++ show ga) $ return True
  return ()

qpr :: [String] -- inductively what?
    -> Tm       -- size zone
    -> ( ([(Nom, (Nom, Hide Tm))], Tm)
       , ([((Nom, Hide Tm), String)], Tm)
       )  -- wees, bigs
    -> AM  ( ([(Nom, (Nom, Hide Tm))], Tm)
           , ([((Nom, Hide Tm), String)], Tm)
           )  -- wees, bigs
qpr xs z v@((ws, wg), (bs, bg)) = pop (const True) >>= \case
  Nothing -> gripe Mardiness
  Just DoorStop -> case xs of
    [] -> v <$ push DoorStop
    x : _ -> gripe $ Scope x
  Just (Bind yp@(yn, Hide ty) (User y)) -> case partition (y ==) xs of
    ([], _) -> do
      ty <- norm ty
      wyn <- fresh y
      let wy = (wyn, Hide ty)
      qpr xs z
        ( ((yn, wy) : map (id *** (id *** e4p (yn, TP wy))) ws, e4p (yn, TP wy) wg)
        , ((yp, y) : bs, bg)
        )
    (_, xs) -> hnf ty >>= \ ty -> case ty of
      TC d ss -> do
        wyn <- fresh y
        cope (isDataType d) (\ _ -> gripe $ NotADataType ty) return
        let wy = (wyn, Hide (TC "$" [ty, z, TC "S" [TC "Z" []]]))
        let by = (yn, Hide (TC "$" [ty, z, TC "Z" []]))
        qpr xs z
          ( ((yn, wy) : map (id *** (id *** e4p (yn, TP wy))) ws, e4p (yn, TP wy) wg)
          , ((by, y) : map ((id *** e4p (yn, TP by)) *** id) bs, e4p (yn, TP by) bg)
          )
  Just (Bind (yn, Hide ty) (Defn tm)) -> qpr xs z
    ( (map (id *** (id *** e4p (yn, tm ::: ty))) ws, e4p (yn, tm ::: ty) wg)
    , (map ((id *** e4p (yn, tm ::: ty)) *** id) bs, e4p (yn, tm ::: ty) bg)
    )
  Just (Bind yp@(yn, Hide ty) Hole) -> qpr xs z
    ( (ws, wg)
    , ((yp, "") : bs, bg)
    )
  _ -> qpr xs z v
        