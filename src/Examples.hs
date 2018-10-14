module Examples
where

import Fbpmn

--
-- g1
--
-- NSE -> + {T1, T2} + -> NEE
--
g1 :: BpmnGraph
g1 = mkGraph
  ["Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
 where
  catN = fromList
    [ ("Start"   , NoneStartEvent)
    , ("SplitAnd", AndGateway)
    , ("T1a"     , AbstractTask)
    , ("T2a"     , AbstractTask)
    , ("T1b"     , AbstractTask)
    , ("T2b"     , AbstractTask)
    , ("JoinAnd" , AndGateway)
    , ("End"     , NoneEndEvent)
    ]
  catE = fromList
    [ ("e1"  , NormalSequenceFlow)
    , ("es+a", NormalSequenceFlow)
    , ("es+b", NormalSequenceFlow)
    , ("e2a" , NormalSequenceFlow)
    , ("e2b" , NormalSequenceFlow)
    , ("ej+a", NormalSequenceFlow)
    , ("ej+b", NormalSequenceFlow)
    , ("e3"  , NormalSequenceFlow)
    ]
  source = fromList
    [ ("e1"  , "Start")
    , ("es+a", "SplitAnd")
    , ("es+b", "SplitAnd")
    , ("e2a" , "T1a")
    , ("e2b" , "T1b")
    , ("ej+a", "T2a")
    , ("ej+b", "T2b")
    , ("e3"  , "JoinAnd")
    ]
  target = fromList
    [ ("e1"  , "SplitAnd")
    , ("es+a", "T1a")
    , ("es+b", "T1b")
    , ("e2a" , "T2a")
    , ("e2b" , "T2b")
    , ("ej+a", "JoinAnd")
    , ("ej+b", "JoinAnd")
    , ("e3"  , "End")
    ]
  name = fromList []

