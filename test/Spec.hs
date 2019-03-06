import           Test.Tasty
import           Test.Tasty.HUnit
-- import           Test.Tasty.QuickCheck as QC
-- import           Test.Tasty.SmallCheck as SC
import           Test.Tasty.Runners.Html

import           Fbpmn.Model
import           Examples                       ( g0
                                                , g1
                                                )

main :: IO ()
main = defaultMainWithIngredients (htmlRunner : defaultIngredients) test

test :: TestTree
test = testGroup "Tests" [mainTests]

mainTests :: TestTree
mainTests = testGroup "Main tests" [unittests]

unittests :: TestTree
unittests =
  testGroup "Unit tests" [uIsValidGraph, uNodesT, uEdgesT, uInN, uOutN]

uIsValidGraph :: TestTree
uIsValidGraph = testGroup
  "Unit tests for isValidGraph"
  [ testCase "all ok" $ isValidGraph g0 @?= True
  , testCase "wrong message flow" $ isValidGraph g0e1 @?= False
  , testCase "wrong message flow" $ isValidGraph g0e2 @?= False
  , testCase "missing catN" $ isValidGraph g0a @?= False
  , testCase "missing catE" $ isValidGraph g0b @?= False
  , testCase "missing sourceE" $ isValidGraph g0c @?= False
  , testCase "missing targetE" $ isValidGraph g0d @?= False
  , testCase "all ok" $ isValidGraph g1 @?= True
  ]

uNodesT :: TestTree
uNodesT = testGroup
  "Unit tests for nodesT"
  [ testCase "empty" $ nodesT g1 SendTask @?= []
  , testCase "non empty, direct"
  $   nodesT g1 AbstractTask
  @?= ["T1a", "T1b", "T2a", "T2b"]
  ]

uEdgesT :: TestTree
uEdgesT = testGroup
  "Unit tests for edgesT"
  [ testCase "empty" $ edgesT g1 MessageFlow @?= []
  , testCase "non empty, direct"
  $   edgesT g1 NormalSequenceFlow
  @?= ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  ]

uInN :: TestTree
uInN = testGroup
  "Unit tests for inN"
  [ testCase "empty" $ inN g1 "Start" @?= []
  , testCase "non empty" $ inN g1 "JoinAnd" @?= ["ej+a", "ej+b"]
  ]

uOutN :: TestTree
uOutN = testGroup
  "Unit tests for outN"
  [ testCase "empty" $ outN g1 "End" @?= []
  , testCase "non empty" $ outN g1 "SplitAnd" @?= ["es+a", "es+b"]
  ]

--
-- graphs
--

g0a :: BpmnGraph
g0a = mkGraph
  "g0a"
  ["Process", "Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
  containN
  containE
  []
  (fromList [])
 where
  catN = fromList
    [ ("Process" , Process)
    , ("Start"   , NoneStartEvent)
    , ("SplitAnd", AndGateway)
    , ("T1a"     , AbstractTask)
    , ("T2a"     , AbstractTask)
    , ("T1b"     , AbstractTask)
    , ( "T2b"
      , AbstractTask
      )
--    , ("JoinAnd" , AndGateway)
    , ("End", NoneEndEvent)
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
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]

g0b :: BpmnGraph
g0b = mkGraph
  "g0b"
  ["Process", "Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
  containN
  containE
  []
  (fromList [])
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
    , ( "e2b"
      , NormalSequenceFlow
      )
--    , ("ej+a", NormalSequenceFlow)
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
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]

g0c :: BpmnGraph
g0c = mkGraph
  "g0c"
  ["Process", "Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
  containN
  containE
  []
  (fromList [])
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
    , ( "e2b"
      , "T1b"
      )
--    , ("ej+a", "T2a")
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
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]

g0d :: BpmnGraph
g0d = mkGraph
  "g0d"
  ["Process", "Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
  name
  containN
  containE
  []
  (fromList [])
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
    , ( "e2b"
      , "T2b"
      )
--    , ("ej+a", "JoinAnd")
    , ("ej+b", "JoinAnd")
    , ("e3"  , "End")
    ]
  name = fromList []
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]

g0e1 :: BpmnGraph
g0e1 = mkGraph "g0e1"
               ["Sender", "Receiver", "NSE1", "NSE2", "ST1", "RT2", "NEE1", "NEE2"]
               ["a", "b", "c", "d", "m"]
               catN
               catE
               source
               target
               name
               containN
               containE
               ["message"]
               (fromList [("m", "message")])
              where
  catN = fromList
    [ ("Sender" , Process)
    , ("Receiver" , Process)
    , ("NSE1", NoneStartEvent)
    , ("NSE2", NoneStartEvent)
    , ("ST1" , SendTask)
    , ("RT2" , ReceiveTask)
    , ("NEE1", NoneEndEvent)
    , ("NEE2", NoneEndEvent)
    ]
  catE = fromList
    [ ("a", NormalSequenceFlow)
    , ("b", NormalSequenceFlow)
    , ("c", NormalSequenceFlow)
    , ("d", NormalSequenceFlow)
    , ("m", MessageFlow)
    ]
  source = fromList
    [("a", "NSE1"), ("b", "ST1"), ("c", "NSE2"), ("d", "RT2"), ("m", "NSE1")]
  target = fromList
    [("a", "ST1"), ("b", "NEE1"), ("c", "RT2"), ("d", "NEE2"), ("m", "RT2")]
  name = fromList []
  containN = fromList
    [("Sender", ["NSE1", "ST1", "NEE1"]), ("Receiver", ["NSE2", "RT2", "NEE2"])]
  containE = fromList [("Sender", ["a", "b"]), ("Receiver", ["c", "d"])]

g0e2 :: BpmnGraph
g0e2 = mkGraph "g0e2"
               ["Sender", "Receiver", "NSE1", "NSE2", "ST1", "RT2", "NEE1", "NEE2"]
               ["a", "b", "c", "d", "m"]
               catN
               catE
               source
               target
               name
               containN
               containE
               ["message"]
               (fromList [("m", "message")])
 where
  catN = fromList
    [ ("Sender" , Process)
    , ("Receiver" , Process)
    , ("NSE1", NoneStartEvent)
    , ("NSE2", NoneStartEvent)
    , ("ST1" , SendTask)
    , ("RT2" , ReceiveTask)
    , ("NEE1", NoneEndEvent)
    , ("NEE2", NoneEndEvent)
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
    [("a", "ST1"), ("b", "NEE1"), ("c", "RT2"), ("d", "NEE2"), ("m", "NEE2")]
  name = fromList []
  containN = fromList
    [("Sender", ["NSE1", "ST1", "NEE1"]), ("Receiver", ["NSE2", "RT2", "NEE2"])]
  containE = fromList [("Sender", ["a", "b"]), ("Receiver", ["c", "d"])]
