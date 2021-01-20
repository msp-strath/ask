module Ask.Src.HardwiredRules where

import qualified Data.Map as M

import Ask.Src.Tm
import Ask.Src.RawAsk
import Ask.Src.Scoping

mySetup :: Setup
mySetup = Setup
  { introRules = myIntroRules
  , weirdRules = myWeirdRules
  , fixities   = myFixities
  }

myFixities :: FixityTable
myFixities = M.fromList
  [ ("&", (7, RAsso))
  , ("|", (6, RAsso))
  , ("->", (1, RAsso))
  ]

myIntroRules :: [Rule]
myIntroRules =
  [ (PC "&" [PM "a" mempty, PM "b" mempty], PC "AndI" []) :<=
    [ TC "prove" [TM "a" []]
    , TC "prove" [TM "b" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], PC "OrIL" []) :<=
    [ TC "prove" [TM "a" []]
    ]
  , (PC "|" [PM "a" mempty, PM "b" mempty], PC "OrIR" []) :<=
    [ TC "prove" [TM "b" []]
    ]
  , (PC "->" [PM "a" mempty, PM "b" mempty], PC "ImpI" []) :<=
    [ TC "given" [TM "a" [], TC "prove" [TM "b" []]]
    ]
  , (PC "Not" [PM "a" mempty], PC "NotI" []) :<=
    [ TC "given" [TM "a" [], TC "prove" [TC "False" []]]
    ]
  , (PC "True" [], PC "TrueI" []) :<= []
  ]

myWeirdRules :: [Rule]
myWeirdRules =
  [ (PM "x" mempty, PC "Contradiction" []) :<=
    [ TC "given" [TC "Not" [TM "x" []],
      TC "prove" [TC "False" []]]
    ]
  ]
