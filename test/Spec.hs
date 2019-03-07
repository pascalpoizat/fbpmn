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
  testGroup "Unit tests" [uIsValidGraph, uNodesT, uEdgesT, uInN, uOutN, uPredecessorEdges, uPre]

uIsValidGraph :: TestTree
uIsValidGraph = testGroup
  "Unit tests for isValidGraph"
  [ testCase "all ok g1" $ isValidGraph g0 @?= True
  , testCase "all ok g2" $ isValidGraph g2 @?= True
  , testCase "all ok g3" $ isValidGraph g3 @?= True
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

uPredecessorEdges :: TestTree
uPredecessorEdges = testGroup
  "Unit tests of predecessorEdges"
  [ testCase "general e0"  $ predecessorEdges g2 "e0"  @?= []
  , testCase "general e1"  $ predecessorEdges g2 "e1"  @?= ["e0", "e15"]
  , testCase "general e2"  $ predecessorEdges g2 "e2"  @?= ["e1"]
  , testCase "general e3"  $ predecessorEdges g2 "e3"  @?= ["e2"]
  , testCase "general e4"  $ predecessorEdges g2 "e4"  @?= ["e2"] 
  , testCase "general e5"  $ predecessorEdges g2 "e5"  @?= ["e4"]
  , testCase "general e6"  $ predecessorEdges g2 "e6"  @?= ["e3", "e8"]
  , testCase "general e7"  $ predecessorEdges g2 "e7"  @?= ["e6"]
  , testCase "general e8"  $ predecessorEdges g2 "e8"  @?= ["e7"]
  , testCase "general e9"  $ predecessorEdges g2 "e9"  @?= ["e7"]
  , testCase "general e10" $ predecessorEdges g2 "e10" @?= ["e12", "e5", "e9"]
  , testCase "general e11" $ predecessorEdges g2 "e11" @?= ["e10"]
  , testCase "general e12" $ predecessorEdges g2 "e12" @?= ["e11"]
  , testCase "general e13" $ predecessorEdges g2 "e13" @?= ["e11"]
  , testCase "general e14" $ predecessorEdges g2 "e14" @?= ["e13"]
  , testCase "general e15"  $ predecessorEdges g2 "e15"  @?= ["e2"]
  ]

uPre :: TestTree
uPre = testGroup
  "Unit tests for preE"
  [ testCase "general e5"  $ preE g2 "Or1" "e2"  @?= ["e0", "e1", "e15"]
  , testCase "general e5"  $ preE g2 "Or2" "e5"  @?= ["e0", "e1", "e15", "e2", "e4"]
  , testCase "general e9"  $ preE g2 "Or2" "e9"  @?= ["e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"]
  , testCase "general e10" $ preE g2 "Or2" "e10" @?= []
  , testCase "general e11" $ preE g2 "Or2" "e11" @?= ["e10"]
  , testCase "general e12" $ preE g2 "Or2" "e12" @?= ["e10", "e11"]
  --
  , testCase "with communication e5"  $ preE g3 "Or1" "e2"  @?= ["e0", "e1", "e15"]
  , testCase "with communication e5"  $ preE g3 "Or2" "e5"  @?= ["e0", "e1", "e15", "e2", "e4"]
  , testCase "with communication e9"  $ preE g3 "Or2" "e9"  @?= ["e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"]
  , testCase "with communication e10" $ preE g3 "Or2" "e10" @?= []
  , testCase "with communication e11" $ preE g3 "Or2" "e11" @?= ["e10"]
  , testCase "with communication e12" $ preE g3 "Or2" "e12" @?= ["e10", "e11"]
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

g2 :: BpmnGraph
g2 = mkGraph "g2"
    ["Process", "NSE", "Xor0", "AT1", "Or1", "Xor1", "AT2", "Xor2", "AT3", "Or2", "AT4", "Xor3", "AT5", "NEE"]
    ["e0", "e1", "e2", "e3", "e4", "e5", "e6", "e7", "e8", "e9", "e10", "e11", "e12", "e13", "e14", "e15"]
    catN
    catE
    source
    target
    (fromList [])
    containN
    containE
    []
    (fromList [])
  where
    catN = fromList
      [ ("Process" , Process)
      , ("NSE", NoneStartEvent)
      , ("AT1", AbstractTask)
      , ("Xor0", XorGateway)
      , ("Or1" , OrGateway)
      , ("Xor1" , XorGateway)
      , ("AT2", AbstractTask)
      , ("Xor2", XorGateway)
      , ("AT3", AbstractTask)
      , ("Or2", OrGateway)
      , ("AT4", AbstractTask)
      , ("Xor3", XorGateway)
      , ("AT5", AbstractTask)
      , ("NEE", NoneEndEvent)
      ]
    catE = fromList
      [ ("e0", NormalSequenceFlow)
      , ("e1", NormalSequenceFlow)
      , ("e2", NormalSequenceFlow)
      , ("e3", ConditionalSequenceFlow)
      , ("e4", ConditionalSequenceFlow)
      , ("e5", NormalSequenceFlow)
      , ("e6", NormalSequenceFlow)
      , ("e7", NormalSequenceFlow)
      , ("e8", DefaultSequenceFlow)
      , ("e9", ConditionalSequenceFlow)
      , ("e10", NormalSequenceFlow)
      , ("e11", NormalSequenceFlow)
      , ("e12", DefaultSequenceFlow)
      , ("e13", ConditionalSequenceFlow)
      , ("e14", NormalSequenceFlow)
      , ("e15", DefaultSequenceFlow)
      ]
    source = fromList
      [ ("e0", "NSE")
      , ("e1", "Xor0")
      , ("e2", "AT1")
      , ("e3", "Or1")
      , ("e4", "Or1")
      , ("e5", "AT3")
      , ("e6", "Xor1")
      , ("e7", "AT2")
      , ("e8", "Xor2")
      , ("e9", "Xor2")
      , ("e10", "Or2")
      , ("e11", "AT4")
      , ("e12", "Xor3")
      , ("e13", "Xor3")
      , ("e14", "AT5")
      , ("e15", "Or1")
      ]
    target = fromList
      [ ("e0", "Xor0")
      , ("e1", "AT1")
      , ("e2", "Or1")
      , ("e3", "Xor1")
      , ("e4", "AT3")
      , ("e5", "Or2")
      , ("e6", "AT2")
      , ("e7", "Xor2")
      , ("e8", "Xor1")
      , ("e9", "Or2")
      , ("e10", "AT4")
      , ("e11", "Xor3")
      , ("e12", "Or2")
      , ("e13", "AT5")
      , ("e14", "NEE")
      , ("e15", "Xor0")
      ]
    containN = fromList
      [("Process", ["NSE", "AT1", "Xor0", "Or1", "Xor1", "AT2", "Xor2", "AT3", "Or2", "AT4", "Xor3", "AT5", "NEE"])]
    containE = fromList
      [("Process", ["e0", "e1", "e2", "e3", "e4", "e5", "e6", "e7", "e8", "e9", "e10", "e11", "e12", "e13", "e14", "e15"])]

g3 :: BpmnGraph
g3 = mkGraph "g3"
    ["Process", "NSE", "Xor0", "AT1", "Or1", "Xor1", "AT2", "Xor2", "RT3", "Or2", "AT4", "Xor3", "AT5", "NEE"
    ,"Sender", "NSE2", "ST1", "NEE2"]
    ["e0", "e1", "e2", "e3", "e4", "e5", "e6", "e7", "e8", "e9", "e10", "e11", "e12", "e13", "e14", "e15"
    ,"e16", "e17"
    ,"mf1"]
    catN
    catE
    source
    target
    (fromList [])
    containN
    containE
    ["message"]
    (fromList [("mf1", "message")])
  where
    catN = fromList
      [ ("Process" , Process)
      , ("NSE", NoneStartEvent)
      , ("AT1", AbstractTask)
      , ("Xor0", XorGateway)
      , ("Or1" , OrGateway)
      , ("Xor1" , XorGateway)
      , ("AT2", AbstractTask)
      , ("Xor2", XorGateway)
      , ("RT3", ReceiveTask)
      , ("Or2", OrGateway)
      , ("AT4", AbstractTask)
      , ("Xor3", XorGateway)
      , ("AT5", AbstractTask)
      , ("NEE", NoneEndEvent)
      , ("Sender", Process)
      , ("NSE2", NoneStartEvent)
      , ("ST1", SendTask)
      , ("NEE2", NoneEndEvent)
      ]
    catE = fromList
      [ ("e0", NormalSequenceFlow)
      , ("e1", NormalSequenceFlow)
      , ("e2", NormalSequenceFlow)
      , ("e3", ConditionalSequenceFlow)
      , ("e4", ConditionalSequenceFlow)
      , ("e5", NormalSequenceFlow)
      , ("e6", NormalSequenceFlow)
      , ("e7", NormalSequenceFlow)
      , ("e8", DefaultSequenceFlow)
      , ("e9", ConditionalSequenceFlow)
      , ("e10", NormalSequenceFlow)
      , ("e11", NormalSequenceFlow)
      , ("e12", DefaultSequenceFlow)
      , ("e13", ConditionalSequenceFlow)
      , ("e14", NormalSequenceFlow)
      , ("e15", DefaultSequenceFlow)
      , ("e16", NormalSequenceFlow)
      , ("e17", NormalSequenceFlow)
      , ("mf1", MessageFlow)
      ]
    source = fromList
      [ ("e0", "NSE")
      , ("e1", "Xor0")
      , ("e2", "AT1")
      , ("e3", "Or1")
      , ("e4", "Or1")
      , ("e5", "RT3")
      , ("e6", "Xor1")
      , ("e7", "AT2")
      , ("e8", "Xor2")
      , ("e9", "Xor2")
      , ("e10", "Or2")
      , ("e11", "AT4")
      , ("e12", "Xor3")
      , ("e13", "Xor3")
      , ("e14", "AT5")
      , ("e15", "Or1")
      , ("e16", "NSE2")
      , ("e17", "ST1")
      , ("mf1", "ST1")
      ]
    target = fromList
      [ ("e0", "Xor0")
      , ("e1", "AT1")
      , ("e2", "Or1")
      , ("e3", "Xor1")
      , ("e4", "RT3")
      , ("e5", "Or2")
      , ("e6", "AT2")
      , ("e7", "Xor2")
      , ("e8", "Xor1")
      , ("e9", "Or2")
      , ("e10", "AT4")
      , ("e11", "Xor3")
      , ("e12", "Or2")
      , ("e13", "AT5")
      , ("e14", "NEE")
      , ("e15", "Xor0")
      , ("e16", "ST1")
      , ("e17", "NEE2")
      , ("mf1", "RT3")
      ]
    containN = fromList
      [("Process", ["NSE", "AT1", "Xor0", "Or1", "Xor1", "AT2", "Xor2", "AT3", "Or2", "AT4", "Xor3", "AT5", "NEE"])
      ,("Sender", ["NSE2", "ST1", "NEE2"])]
    containE = fromList
      [("Process", ["e0", "e1", "e2", "e3", "e4", "e5", "e6", "e7", "e8", "e9", "e10", "e11", "e12", "e13", "e14", "e15"])
      ,("Sender", ["e16", "e17"])]
