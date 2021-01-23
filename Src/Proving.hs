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
by goal a@(_, (t, _, s) :$$ _) | elem t [Uid, Sym] = do
  subses <- fold <$> (gamma >>= traverse (backchain a))
  case subses of
    [(t, subs)] -> do
      mapM_ demand subs
      return t
    []     -> gripe $ ByBadRule s goal
    _      -> gripe $ ByAmbiguous s goal
 where
  backchain :: Appl -> CxE -> AM [(TmR, [Subgoal])] -- list of successes
  backchain a@(_, (_, _, r) :$$ ss) (ByRule _ ((gop, (h, tel)) :<= prems))
    | h == r = do
    m <- maAM (gop, goal)
    cope ((`Our` a) <$> elabTel h (stan m tel) ss) (\ _ -> return []) $ \ t ->
      return [(t, stan m prems)]
  backchain _ _ = return []
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
