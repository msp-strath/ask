module Ask.Src.HardwiredRules where

import qualified Data.Map as M

import Ask.Src.Bwd
import Ask.Src.Tm
import Ask.Src.RawAsk
import Ask.Src.Context

mySetup :: Setup
mySetup = Setup
  { fixities   = myFixities
  }

myFixities :: FixityTable
myFixities = M.fromList
  [ ("&", (7, RAsso))
  , ("|", (6, RAsso))
  , ("->", (1, RAsso))
  ]

myPreamble :: Bwd Entry
myPreamble = B0
  :< Ctor (("Type", "Type") :- Re . Re $ Ok)
  :< Ctor (("Type", "Prop") :- Re . Re $ Ok)
  :< Data (("Type", "'Sigma") :- Re .
             Expl Type . L . Expl (TE (TV 0) :-> Type) . K . Re $ Ok)
          [("'Sigma", "(,)") :-
             Expl Type . L . Expl (TE (TV 0) :-> Type) . L . Re .
             Expl (TE (TV 1)) . L . Expl (TE (TV 1 :$ TE (TV 0))) . K . Re $ Ok
          ]
  :< Ctor (("Type", "->") :- Re . Expl Type . K . Expl Type . K . Re $ Ok)
  :< Ctor (("Prop", "=") :-
       Re . Impl Type . L . Expl (TE (TV 0)) . K . Expl (TE (TV 0)) . K .
       Re $ Ok)
  :< Ctor (("Prop", "'<=") :- Re . Expl Type . K . Expl Type . K . Re $ Ok)
  :< Ctor (("Prop", "'Defd") :- Re . Expl Type . L . Expl (TE (TV 0)) . K .
       Re $ Ok)
  :< Conn (("Prop", "False") :- Re . Re $ Ok) []
  :< Conn (("Prop", "True") :- Re . Re $ Ok)
       [ ("True", "TrueI") :- Re . Re $ Nil
       ]
  :< Conn (("Prop", "->") :- Re . Expl Prop . K . Expl Prop . K . Re $ Ok)
       [ ("->", "ImpI") :- Expl Prop . L . Expl Prop . L . Re .
         Cons (GIVEN (TE (TV 1)) $ PROVE (TE (TV 0))) $
         Nil
       ]
  :< Conn (("Prop", "&") :- Re . Expl Prop . K . Expl Prop . K . Re $ Ok)
       [ ("&", "AndI") :- Expl Prop . L . Expl Prop . L . Re .
         Cons (PROVE (TE (TV 1))) .
         Cons (PROVE (TE (TV 0))) $
         Nil
       ]
  :< Conn (("Prop", "|") :- Re . Expl Prop . K . Expl Prop . K . Re $ Ok)
       [ ("|", "OrIL") :- Expl Prop . L . Expl Prop . K . Re .
         Cons (PROVE (TE (TV 0))) $
         Nil
       , ("|", "OrIR") :- Expl Prop . K . Expl Prop . L . Re .
         Cons (PROVE (TE (TV 0))) $
         Nil
       ]
  :< Conn (("Prop", "Not") :- Re . Expl Prop . K . Re $ Ok)
       [ ("Not", "NotI") :- Expl Prop . L . Re .
         Cons (GIVEN (TE (TV 0)) $ PROVE FALSE) $
         Nil
       ]
  :< Admit "Contradiction" (L . Re .
       Cons (GIVEN (TC "Not" [TE (TV 0)]) $ PROVE FALSE) $
       Nil
       )
