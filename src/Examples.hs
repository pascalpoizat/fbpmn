module Examples where

import           Fbpmn.BpmnGraph.Model

models' :: [BpmnGraph]
models' = [g0, g1]

models :: Map Text BpmnGraph
models = fromList $ f <$> models' where f g = (name g, g)

--
-- g0
--
-- SEND/RECEIVE
--
g0 :: BpmnGraph
g0 = mkGraph
  "g0"
  ["Sender", "Receiver", "NSE1", "NSE2", "ST1", "RT2", "NEE1", "NEE2"]
  ["a", "b", "c", "d", "m"]
  catN
  catE
  source
  target
  name
  containN
  containE
  attached
  messages
  messageE
  isInterrupt
  timeInformation
 where
  catN = fromList
    [ ("Sender"  , Process)
    , ("Receiver", Process)
    , ("NSE1"    , NoneStartEvent)
    , ("NSE2"    , NoneStartEvent)
    , ("ST1"     , SendTask)
    , ("RT2"     , ReceiveTask)
    , ("NEE1"    , NoneEndEvent)
    , ("NEE2"    , NoneEndEvent)
    ]
  catE = fromList
    [ ("a", NormalSequenceFlow)
    , ("b", NormalSequenceFlow)
    , ("c", NormalSequenceFlow)
    , ("d", NormalSequenceFlow)
    , ("m", MessageFlow)
    ]
  source = fromList
    [("a", "NSE1"), ("b", "ST1"), ("c", "NSE2"), ("d", "RT2"), ("m", "ST1")]
  target = fromList
    [("a", "ST1"), ("b", "NEE1"), ("c", "RT2"), ("d", "NEE2"), ("m", "RT2")]
  name     = fromList []
  containN = fromList
    [("Sender", ["NSE1", "ST1", "NEE1"]), ("Receiver", ["NSE2", "RT2", "NEE2"])]
  containE = fromList [("Sender", ["a", "b"]), ("Receiver", ["c", "d"])]
  attached = fromList []
  messages = ["message"]
  messageE = fromList [("m", "message")]
  isInterrupt = fromList []
  timeInformation = fromList []

--
-- g1
--
-- NSE -> + {T1, T2} + -> NEE
--
g1 :: BpmnGraph
g1 = mkGraph
  "g1"
  ["Process", "Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
  containN
  containE
  attached
  messages
  messageN
  isInterrupt
  timeInformation
 where
  catN = fromList
    [ ("Process" , Process)
    , ("Start"   , NoneStartEvent)
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
  name     = fromList []
  containN = fromList
    [ ( "Process"
      , ["Start", "End", "SplitAnd", "JoinAnd", "T1a", "T1b", "T2a", "T2b"]
      )
    ]
  containE = fromList
    [("Process", ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"])]
  attached = fromList []
  messages = []
  messageN = fromList []
  isInterrupt = fromList []
  timeInformation = fromList []

