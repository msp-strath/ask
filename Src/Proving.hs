------------------------------------------------------------------------------
----------                                                          ----------
----------     Ask.Src.Proving                                      ----------
----------                                                          ----------
------------------------------------------------------------------------------

{-# LANGUAGE
    LambdaCase
#-}

module Ask.Src.Proving where

import Data.Foldable

import Ask.Src.Hide
import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Glueing
import Ask.Src.Context
import Ask.Src.Typing

by :: Tm -> Appl -> AM TmR
by goal a@(_, (t, _, r) :$$ ss) | elem t [Uid, Sym] = do
  subses <- fold <$> (gamma >>= traverse backchain)
  case subses of
    [(tel, subs)] -> do
      (t, m) <- elabVec r tel ss
      mapM_ fred (stan m subs)
      return $ Our t a
    []     -> gripe $ ByBadRule r goal
    _      -> gripe $ ByAmbiguous r goal
 where
  backchain :: CxE -> AM [(Tel, [Subgoal])] -- list of successes
  backchain (ByRule _ ((gop, (h, tel)) :<= prems))
    | h == r = 
    cope (do
      m <- maAM (gop, goal)
      return [(stan m tel, stan m prems)])
      (\ _ -> return [])
      return
  backchain _ = return []
by goal r = gripe $ NotARule r

invert :: Tm -> AM [((String, Tel), [Subgoal])]
invert hyp = fold <$> (gamma >>= traverse try )
 where
  try :: CxE -> AM [((String, Tel), [Subgoal])]
  try (ByRule True ((gop, (h, tel)) :<= prems)) = cope (maAM (gop, hyp))
    (\ _ -> return [])
    (\ m -> return [((h, stan m tel), stan m prems)])
  try _ = return []

given :: Tm -> AM ()
given goal = gamma >>= go where
  go B0 = gripe $ NotGiven goal
  go (ga :< Hyp hyp) = cope (unify (TC "Prop" []) hyp goal)
    (\ gr -> go ga) return
  go (ga :< _) = go ga

(|-) :: Tm -> AM x -> AM x
h |- p = do
  push (Hyp h)
  x <- p
  pop $ \case
    Hyp _ -> True
    _ -> False
  return x

splitProof
  :: (Nom, Hide Tm) -- thing to split
  -> (Con, [Tm])
  -> Tm  -- goal
  -> CxE -- constructor (we hope)
  -> AM () -- generate relevant demands
splitProof xp@(xn, _) (d, ss) goal ((d', ps) ::> (c, _)) | d == d' =
  cope (constructor (TC d ss) c) (\ _ -> return ()) $ \ tel ->
    quan B0 tel >>= fred
 where
  quan :: Bwd Tm -> Tel -> AM Subgoal
  quan sz (Ex s b) =
    ("", s) |:- \ e@(TP (yn, _)) ->
      (EVERY s . (yn \\)) <$> quan (sz :< TE e) (b // e)
  quan sz ((y, s) :*: tel) =
    (y, s) |:- \ e@(TP (yn, _)) ->
      (EVERY s . (yn \\)) <$> quan (sz :< TE e) (stan [(y, TE e)] tel)
  quan sz (Pr hs) = let ty = TC d ss; tm = TC c (sz <>> []) in
    return $ foldr GIVEN
      (GIVEN (TC "=" [ty, TE (TP xp), tm]) $
         PROVE ((xn \\ goal) // (tm ::: ty)))
      hs
    
  
splitProof _ _ _ _ = return ()
  