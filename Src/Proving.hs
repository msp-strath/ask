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
  go (ga :< Hyp hyp) = cope (equal (TC "Prop" []) (hyp, goal))
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
