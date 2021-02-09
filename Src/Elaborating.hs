------------------------------------------------------------------------------
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

import Ask.Src.Bwd
import Ask.Src.Lexing
import Ask.Src.RawAsk
import Ask.Src.Tm
import Ask.Src.Context
import Ask.Src.Computing

{-
data Elab
  = NoElab
  | ElabTop
  | ElabDecl RawDecl
  deriving Show
-}


------------------------------------------------------------------------------
--  Elaboration Outcomes
------------------------------------------------------------------------------

data Outcome
  = Defn (Bwd Entry) Tm  -- this is a success
  | Stuk Request Elab
  | Bork
  | Stay
  deriving Show

elaborate {- dalek voice -} :: AM Outcome
elaborate = problem >>= \case
  ElabDecl r -> case r of
    RawProof p -> topSubMake p
    RawSewage -> return Bork
    _ -> return $ Defn B0 TRUE
  _ -> return $ Stay


------------------------------------------------------------------------------
--  Proof/Program elaboration
------------------------------------------------------------------------------

topSubMake :: SubMake () Appl -> AM Outcome
topSubMake ((_, gs) ::- Make k g m a sps src) = case k of
  Def -> return Bork -- for now
  Prf -> do
    push ImplicitForall
    traverse elabGiven gs
    goal <- chkElab "G" Prop g
    undefined

elabGiven :: Given Appl -> AM ()
elabGiven (Given h) = do
  hyp <- chkElab "H" Prop h
  push (Hyp hyp)



------------------------------------------------------------------------------
--  Terms
------------------------------------------------------------------------------

chkElab :: String -> Ty -> Appl -> AM Tm
chkElab x ty (src, (_, _, f) :$$ as) = undefined


------------------------------------------------------------------------------
--  Machinery
------------------------------------------------------------------------------

topol :: (Layer -> AM x) -> AM x
topol f = do
  l <- AM $ \ _ lz@(_ :< l) -> Right (l, lz)
  f l

topov :: (Layer -> AM x) -> AM x
topov f = do
  l <- AM $ \ _ (lz :< l) -> Right (l, lz)
  f l

leave :: Outcome -> AM Syn
leave = \case
  Defn ez v -> do
    l <- topov return
    let d = myDecl l
    e <- (::: typ d) <$> chkHnf (typ d, v)
    let d' = Decl
          { nom = nom d
          , typ = typ d
          , wot = Green (stable v) e
          , who = who d
          }
    push . The $ l {myDecl = d', myStat = Old}
    case myStat l of
      Old -> push . News $ M.singleton (nom d) d'
      _   -> return ()
    return e
  Stuk r p -> do
    undefined
    