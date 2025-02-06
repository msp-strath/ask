module Language.Ask.HardwiredRules where

import qualified Data.Map as M

import Language.Ask.Bwd
import Language.Ask.Tm
import Language.Ask.RawAsk
import Language.Ask.Context

myFixities :: FixityTable
myFixities = M.fromList
  [ ("=", (4, NAsso))
  , ("&", (3, RAsso))
  , ("|", (2, RAsso))
  , ("->", (1, RAsso))
  ]

myPreamble :: Context
myPreamble = B0
  :< (("Type", []) ::> ("Type", Pr []))   -- boo! hiss!
  :< (("Type", []) ::> ("Prop", Pr []))
  :< (("Type", []) ::> ("->", ("s", Type) :*: ("t", Type) :*: Pr []))
  :< (("Prop", []) ::> ("->", ("s", Prop) :*: ("t", Prop) :*: Pr []))
  :< (("Prop", []) ::> ("&", ("s", Prop) :*: ("t", Prop) :*: Pr []))
  :< (("Prop", []) ::> ("|", ("s", Prop) :*: ("t", Prop) :*: Pr []))
  :< (("Prop", []) ::> ("Not", ("s", Prop) :*: Pr []))
  :< (("Prop", []) ::> ("False", Pr []))
  :< (("Prop", []) ::> ("True", Pr []))
  :< (("Prop", []) ::> ("=", Ex Type . L $
                        ("x", TE (TV 0)) :*: ("y", TE (TV 0)) :*: Pr []))

myIntroRules :: [Rule]
myIntroRules =
  [ (PC "&" [PM "a" mempty, PM "b" mempty], ("AndI", Pr [])) :<=
    [ PROVE $ TM "a" []
    , PROVE $ TM "b" []
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIL", Pr [])) :<=
    [ PROVE $ TM "a" []
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIR", Pr [])) :<=
    [ PROVE $ TM "b" []
    ]
  , (PC "->" [PM "a" mempty, PM "b" mempty], ("ImpI", Pr [])) :<=
    [ GIVEN (TM "a" []) . PROVE $ TM "b" []
    ]
  , (PC "Not" [PM "a" mempty], ("NotI", Pr [])) :<=
    [ GIVEN (TM "a" []) . PROVE $ TC "False" []
    ]
  , (PC "True" [], ("TrueI", Pr [])) :<= []
  ]

myWeirdRules :: [Rule]
myWeirdRules =
  [ (PM "x" mempty, ("Contradiction", Pr [])) :<=
    [ GIVEN (TC "Not" [TM "x" []]) $ PROVE FALSE
    ]
  , (PC "=" [PM "T" mempty, PM "r" mempty, PM "t" mempty],
     ("Route", ("s", TM "T" mempty) :*: Pr [])) :<=
    [ PROVE $ TC "=" [TM "T" [], TM "r" [], TM "s" []]
    , PROVE $ TC "=" [TM "T" [], TM "s" [], TM "t" []]
    ]
  , (PC "=" [PC "->" [PM "S" mempty, PM "T" mempty], PM "f" mempty, PM "g" mempty],
     ("Applying", Pr [])) :<=
    [ EVERY (TM "S" []) . L . PROVE $ TC "="
       [ TM "T" []
       , TE ((TM "f" mempty ::: TC "->" [TM "S" mempty, TM "T" mempty]) :$ TE (TV 0))
       , TE ((TM "g" mempty ::: TC "->" [TM "S" mempty, TM "T" mempty]) :$ TE (TV 0))
       ]
    ]
  , (PC "=" [PC "Prop" [], PM "p" mempty, PM "q" mempty],
     ("Equivalence", Pr [])) :<=
      [ GIVEN (TM "p" []) . PROVE $ TM "q" []
      , GIVEN (TM "q" []) . PROVE $ TM "p" []
      ]
  ]

myContext :: Context
myContext = myPreamble
  <>< [ByRule True  r | r <- myIntroRules]
  <>< [ByRule False r | r <- myWeirdRules]

