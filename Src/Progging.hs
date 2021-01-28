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
import Data.List
import Control.Monad

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

proglify :: Nom -> Sch -> AM Proglem
proglify f s = go B0 B0 s where
  go de iz (as :>> t) = do
    ysxs <- traverse (\ (x, s) -> fresh x >>= \ y -> return (y, s, x)) as
    let m = [(x, TE (TP (y, Hide (stan m s)))) | (y, s, x) <- ysxs]
    return $ Proglem
      { localCx = de <>< [Bind xp (User x) | (x, TE (TP xp)) <- m]
      , fNom = f
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
  doorStop
  push ImplicitQuantifier
  (e, ty) <- elabSyn f as
  lox <- doorStep
  z@(f, is, ss, as) <- mayhem $ fnarg e []
  True <- trade (show z) $ return True
  guard $ f == fNom p
  p <- tro lox as p
  True <- trade (show p) $ return True
  nx <- nub <$> ((++)
    <$> dubs lox (map fst $ leftSatu p) ss
    <*> dubs lox (map fst $ leftAppl p) as)
  guard $ length nx == length (nub (map snd nx))
  return $ p {localCx = fmap (redub nx) (localCx p)}
 where
  tro :: [CxE] -> [Tm] -> Proglem -> AM Proglem
  tro lox [] p = return p
  tro lox (TE (TP (yn, _)) : as) p = case [u | Bind (zn, _) (User u) <- lox , yn == zn] of
    [x] -> do
      True <- trade (show x ++ " tro " ++ show (rightTy p)) $ return True
      TC "->" [dom, ran] <- hnf (rightTy p)
      xn <- fresh x
      let xp = (xn, Hide dom)
      tro lox as $ p
        { localCx  = localCx p :< Bind xp (User x)
        , leftAppl = leftAppl p ++ [(TE (TP xp), dom)]
        , rightTy  = ran
        }
    _ -> gripe FAIL
  tro _ _ _ = gripe FAIL
  dubs :: [CxE] -> [Tm] -> [Tm] -> AM [(Nom, String)]
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
--  constructors for a data type
------------------------------------------------------------------------------

conSplit :: Tm -> AM [(Con, Tel)]
conSplit t = do
  z@(monkey, d, ts) <- case t of
    TC "$" [TC d ts, non, num] -> return (weeer d non (TC "S" [num]), d, ts)
    TC d ts -> return (id, d, ts)
    _ -> gripe FAIL
  (foldMap (\case {Data e de | d == e -> [de]; _ -> []}) <$> gamma) >>= \case
    [de] -> concat <$> traverse (refine z) de
 where
  refine :: (Tel -> Tel, Con, [Tm]) -> CxE -> AM [(Con, Tel)]
  refine (monkey, d, ts) ((e, ps) ::> (c, tel)) | d == e = cope (do
    m <- concat <$> ((mayhem $ halfZip ps ts) >>= traverse maAM)
    return [(c, stan m (monkey tel))]
    )
    (\ _ -> return [])
    return
  refine _ _ = return []
  weeer d non num (Ex a tel) = Ex a (fmap (weeer d non num) tel)
  weeer d non num ((x, s) :*: tel) = (x, hit s) :*: weeer d non num tel where
    hit ty@(TC c ts)
      | c == d = TC "$" [TC c (map hit ts), non, num]
      | otherwise = TC c (map hit ts)
    hit t = t
  weeer d non num (Pr pos) = Pr pos