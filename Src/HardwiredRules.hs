module Ask.Src.HardwiredRules where

import qualified Data.Map as M

import Ask.Src.Bwd
import Ask.Src.Tm
import Ask.Src.RawAsk
import Ask.Src.Scoping

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
  :< (("Type", []) ::> ("Prop", []))
  :< (("Prop", []) ::> ("->", [("s", Prop), ("t", Prop)]))
  :< (("Prop", []) ::> ("&", [("s", Prop), ("t", Prop)]))
  :< (("Prop", []) ::> ("|", [("s", Prop), ("t", Prop)]))
  :< (("Prop", []) ::> ("Not", [("s", Prop)]))
  :< (("Prop", []) ::> ("False", []))
  :< (("Prop", []) ::> ("True", []))

myIntroRules :: [Rule]
myIntroRules =
  [ (PC "&" [PM "a" mempty, PM "b" mempty], ("AndI", [])) :<=
    [ TC "prove" [TM "a" []]
    , TC "prove" [TM "b" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIL", [])) :<=
    [ TC "prove" [TM "a" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], ("OrIR", [])) :<=
    [ TC "prove" [TM "b" []]
    ]
  , (PC "->" [PM "a" mempty, PM "b" mempty], ("ImpI", [])) :<=
    [ TC "given" [TM "a" [], TC "prove" [TM "b" []]]
    ]
  , (PC "Not" [PM "a" mempty], ("NotI", [])) :<=
    [ TC "given" [TM "a" [], TC "prove" [TC "False" []]]
    ]
  , (PC "True" [], ("TrueI", [])) :<= []
  ]

myWeirdRules :: [Rule]
myWeirdRules =
  [ (PM "x" mempty, ("Contradiction", [])) :<=
    [ TC "given" [TC "Not" [TM "x" []],
      TC "prove" [TC "False" []]]
    ]
  ]

myContext :: Context
myContext = myPreamble
  <>< [ByRule True  r | r <- myIntroRules]
  <>< [ByRule False r | r <- myWeirdRules]

