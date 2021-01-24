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

myPreamble :: Context
myPreamble = B0
  :< (("Type", []) ::> ("Type", Pr TRUE))   -- boo! hiss!
  :< (("Type", []) ::> ("Prop", Pr TRUE))
  :< (("Prop", []) ::> ("->", ("s", Prop) :*: ("t", Prop) :*: Pr TRUE))
  :< (("Prop", []) ::> ("&", ("s", Prop) :*: ("t", Prop) :*: Pr TRUE))
  :< (("Prop", []) ::> ("|", ("s", Prop) :*: ("t", Prop) :*: Pr TRUE))
  :< (("Prop", []) ::> ("Not", ("s", Prop) :*: Pr TRUE))
  :< (("Prop", []) ::> ("False", Pr TRUE))
  :< (("Prop", []) ::> ("True", Pr TRUE))
  :< (("Prop", []) ::> ("=", Ex Type . L . Ex Type . L $
                        ("x", TE (TV 1)) :*: ("y", TE (TV 0)) :*:
                        Pr (TC "=" [Type, Type, TE (TV 1), TE (TV 0)])))

myIntroRules :: [Rule]
myIntroRules =
  [ (PC "&" [PM "a" mempty, PM "b" mempty], ("AndI", Pr TRUE)) :<=
    [ PROVE $ TM "a" []
    , PROVE $ TM "b" []
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIL", Pr TRUE)) :<=
    [ PROVE $ TM "a" []
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIR", Pr TRUE)) :<=
    [ PROVE $ TM "b" []
    ]
  , (PC "->" [PM "a" mempty, PM "b" mempty], ("ImpI", Pr TRUE)) :<=
    [ GIVEN (TM "a" []) . PROVE $ TM "b" []
    ]
  , (PC "Not" [PM "a" mempty], ("NotI", Pr TRUE)) :<=
    [ GIVEN (TM "a" []) . PROVE $ TC "False" []
    ]
  , (PC "True" [], ("TrueI", Pr TRUE)) :<= []
  ]

myWeirdRules :: [Rule]
myWeirdRules =
  [ (PM "x" mempty, ("Contradiction", Pr TRUE)) :<=
    [ GIVEN (TC "Not" [TM "x" []]) $ PROVE FALSE
    ]
  ]

myContext :: Context
myContext = myPreamble
  <>< [ByRule True  r | r <- myIntroRules]
  <>< [ByRule False r | r <- myWeirdRules]

