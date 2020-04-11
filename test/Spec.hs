{-# LANGUAGE QuasiQuotes #-}
import           NeatInterpolation (text)
import           Test.Tasty
import           Test.Tasty.HUnit
-- import           Test.Tasty.QuickCheck as QC
-- import           Test.Tasty.SmallCheck as SC
import           Test.Tasty.Runners.Html
import           Fbpmn.BpmnGraph.Model
import           Examples                       ( g0
                                                , g1
                                                )
import           Fbpmn.Analysis.Tla.IO.Log
import           Data.Attoparsec.Text
import           Fbpmn.Analysis.Tla.Model

main :: IO ()
main = defaultMainWithIngredients (htmlRunner : defaultIngredients) test

test :: TestTree
test = testGroup "Tests" [mainTests]

mainTests :: TestTree
mainTests = testGroup "Main tests" [unittests]

unittests :: TestTree
unittests = testGroup
  "Unit tests"
  [uIsValidGraph, uNodesT, uEdgesT, uInN, uOutN, uPredecessorEdges, uPre, uLog]

-- parse error (not enough input)
parseNEI :: Either String a
parseNEI = Left "not enough input"

-- parse error (not enough input, letter case)
-- parseLNEI :: Either String a
-- parseLNEI = Left "letter: not enough input"

-- parse error (not enough input, _ case)
parseUNEI :: Either String a
parseUNEI = Left "'_': not enough input"

-- parse error (correct string not found)
parseWS :: Either String a
parseWS = Left "string"

-- parse error (while using takeWhile1)
parseTW1 :: Either String a
parseTW1 = Left "Failed reading: takeWhile1"

state1 :: Text
state1 = [text|
State 12: <Action line 177, col 1 to line 177, col 21 of module e037Comm>
/\ edgemarks = [MessageFlow_1j3ru8z |-> 0, MessageFlow_01l3u25 |-> 1]
/\ net = (<<"Customer_Id", "TravelAgency_Id", "message1">> :> 2 @@ <<"Customer_Id", "TravelAgency_Id", "message2">> :> 1)
/\ nodemarks = [Airline_id |-> 0, Ticket_Order_Received |-> 1]
|]

state1assign :: Map Variable Value
state1assign = fromList [("edgemarks", MapValue (fromList [("MessageFlow_01l3u25",IntegerValue 1),("MessageFlow_1j3ru8z",IntegerValue 0)]))
                        ,("net", BagValue (fromList [(TupleValue [StringValue "Customer_Id",StringValue "TravelAgency_Id",StringValue "message1"],IntegerValue 2),(TupleValue [StringValue "Customer_Id",StringValue "TravelAgency_Id",StringValue "message2"],IntegerValue 1)]))
                        ,("nodemarks",MapValue (fromList [("Airline_id",IntegerValue 0),("Ticket_Order_Received",IntegerValue 1)]))]

stateN :: Text
stateN = [text|
State 29: Stuttering
Finished checking temporal properties in 00s at 2019-04-11 15:37:25
81 states generated, 60 distinct states found, 0 states left on queue.
Finished in 01s at (2019-04-11 15:37:25)
|]

uLog :: TestTree
uLog = testGroup
  "Unit tests for log parsing"
  [ testCase "parse status ok (success)" $ parseOnly parseStatus okLine @?= Right Success
  , testCase "parse status ok (failure)" $ parseOnly parseStatus errorLine1 @?= Right Failure
  , testCase "parse status ko" $ parseOnly parseStatus ("foo" <> errorLine1) @?= parseNEI
  , testCase "parse status ok after skipping lines" $ parseOnly parseStatus ("foo\nbar\n" <> errorLine1) @?= Right Failure
  , testCase "parse variable ok (alpha)" $ parseOnly parseVariable "  f  " @?= Right "f"
  , testCase "parse variable ok (alpha)" $ parseOnly parseVariable "  foo  " @?= Right "foo"
  , testCase "parse variable ok (non alpha)" $ parseOnly parseVariable "  _  " @?= Right "_"
  , testCase "parse variable ok (non alpha)" $ parseOnly parseVariable "  f_123  " @?= Right "f_123"
  , testCase "parse variable ok (non alpha)" $ parseOnly parseVariable "  _123  " @?= Right "_123"
  , testCase "parse variable ko" $ parseOnly parseVariable "       " @?= parseUNEI
  , testCase "parse string ok" $ parseOnly parseString "  \" 1 2 3 \"  " @?= Right " 1 2 3 "
  , testCase "parse string ko" $ parseOnly parseString "     1 2 3     " @?= parseWS
  , testCase "parse string ko" $ parseOnly parseString "               " @?= parseNEI
  , testCase "parse integer ok" $ parseOnly parseInteger " 123 " @?= Right 123
  , testCase "parse integer ko" $ parseOnly parseInteger "     " @?= parseNEI
  , testCase "parse integer ko" $ parseOnly parseInteger " abc " @?= parseTW1
  , testCase "parse tuple (empty)" $ parseOnly parseTuple "<<>>" @?= Right []
  , testCase "parse tuple (empty)" $ parseOnly parseTuple "  <<>>  " @?= Right []
  , testCase "parse tuple (empty)" $ parseOnly parseTuple "  <<  >>  " @?= Right []
  , testCase "parse tuple (non empty)" $ parseOnly parseTuple "<<123,\"foo\",bar>>" @?= Right [IntegerValue 123, StringValue "foo", VariableValue "bar"]
  , testCase "parse tuple (non empty)" $ parseOnly parseTuple "  <<  123  ,  \"foo\"  ,  bar  >>  " @?= Right [IntegerValue 123, StringValue "foo", VariableValue "bar"]
  , testCase "parse map item" $ parseOnly parseMapItem "a|->1" @?= Right ("a", IntegerValue 1)
  , testCase "parse map item" $ parseOnly parseMapItem "  a  |->  <<123,\"foo\",bar>>  " @?= Right ("a", TupleValue [IntegerValue 123, StringValue "foo", VariableValue "bar"])
  , testCase "parse bag item (integer value)" $ parseOnly parseBagItem "<<123,\"foo\",bar>>:>1" @?= Right (TupleValue [IntegerValue 123, StringValue "foo", VariableValue "bar"], IntegerValue 1)
  , testCase "parse bag item (integer value)" $ parseOnly parseBagItem "  <<123,\"foo\",bar>>  :>  1  " @?= Right (TupleValue [IntegerValue 123, StringValue "foo", VariableValue "bar"], IntegerValue 1)
  , testCase "parse bag item (general value)" $ parseOnly parseBagItem "  <<\"id1\", \"id2\">> :> <<\"message\">>  " @?= Right (TupleValue [StringValue "id1", StringValue "id2"], TupleValue [StringValue "message"])
  , testCase "parse assignment" $ parseOnly parseAssignment "/\\ a=1" @?= Right ("a", IntegerValue 1)
  , testCase "parse assignment" $ parseOnly parseAssignment "  /\\  a  =  <<123,\"foo\",bar>>  " @?= Right ("a", TupleValue [IntegerValue 123, StringValue "foo", VariableValue "bar"])
  , testCase "parse map (empty)" $ parseOnly parseMap "[]" @?= Right []
  , testCase "parse map (empty)" $ parseOnly parseMap "  [  ]  " @?= Right []
  , testCase "parse map (non empty)" $ parseOnly parseMap "[foo|->123,bar|->456]" @?= Right [("foo", IntegerValue 123), ("bar", IntegerValue 456)]
  , testCase "parse map (non empty)" $ parseOnly parseMap "  [  foo  |->  123  ,  bar  |->  456  ]  " @?= Right [("foo", IntegerValue 123), ("bar", IntegerValue 456)]
  , testCase "parse bag (empty)" $ parseOnly parseBag "()" @?= Right []
  , testCase "parse bag (empty)" $ parseOnly parseBag "  (  )  " @?= Right []
  , testCase "parse bag (non empty)" $ parseOnly parseBag "(foo:>123@@bar:>456)" @?= Right [(VariableValue "foo", IntegerValue 123), (VariableValue "bar", IntegerValue 456)]
  , testCase "parse bag (non empty)" $ parseOnly parseBag "  (  foo  :>  123  @@  bar  :>  456  )  " @?= Right [(VariableValue "foo", IntegerValue 123), (VariableValue "bar", IntegerValue 456)]
  , testCase "parse bag (general)" $ parseOnly parseBag "  ( <<\"id1\", \"id2\">> :> <<\"message1\">> @@\n<<\"id2\", \"id1\">> :> <<>> )  " @?= Right [(TupleValue [StringValue "id1", StringValue "id2"], TupleValue [StringValue "message1"]), (TupleValue [StringValue "id2", StringValue "id1"], TupleValue [])]
  , testCase "parse value (string)" $ parseOnly parseValue "  \" 1 2 3 \"  " @?= Right (StringValue " 1 2 3 ")
  , testCase "parse value (integer)" $ parseOnly parseValue " 123 " @?= Right (IntegerValue 123)
  , testCase "parse value (variable)" $ parseOnly parseValue " foo " @?= Right (VariableValue "foo")
  , testCase "parse value (tuple)" $ parseOnly parseValue "  <<  123  ,  \"foo\"  ,  bar  >>  " @?= Right (TupleValue [IntegerValue 123, StringValue "foo", VariableValue "bar"])
  , testCase "parse value (map)" $ parseOnly parseValue "  [  foo  |->  123  ,  bar  |->  456  ]  " @?= Right (MapValue . fromList $ [("foo", IntegerValue 123), ("bar", IntegerValue 456)])
  , testCase "parse value (bag)" $ parseOnly parseValue "  (  foo  :>  123  @@  bar  :>  456  )  " @?= Right (BagValue . fromList $ [(VariableValue "foo", IntegerValue 123), (VariableValue "bar", IntegerValue 456)])
  , testCase "parse state (regular)" $ parseOnly parseState state1 @?= Right (CounterExampleState 12 "<Action line 177, col 1 to line 177, col 21 of module e037Comm>" state1assign)
  , testCase "parse state (stuttering)" $ parseOnly parseState stateN @?= Right (CounterExampleState 29 "Stuttering" (fromList []))
  ]

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
  [ testCase "general e0" $ predecessorEdges g2 "e0" @?= []
  , testCase "general e1" $ predecessorEdges g2 "e1" @?= ["e0", "e15"]
  , testCase "general e2" $ predecessorEdges g2 "e2" @?= ["e1"]
  , testCase "general e3" $ predecessorEdges g2 "e3" @?= ["e2"]
  , testCase "general e4" $ predecessorEdges g2 "e4" @?= ["e2"]
  , testCase "general e5" $ predecessorEdges g2 "e5" @?= ["e4"]
  , testCase "general e6" $ predecessorEdges g2 "e6" @?= ["e3", "e8"]
  , testCase "general e7" $ predecessorEdges g2 "e7" @?= ["e6"]
  , testCase "general e8" $ predecessorEdges g2 "e8" @?= ["e7"]
  , testCase "general e9" $ predecessorEdges g2 "e9" @?= ["e7"]
  , testCase "general e10" $ predecessorEdges g2 "e10" @?= ["e12", "e5", "e9"]
  , testCase "general e11" $ predecessorEdges g2 "e11" @?= ["e10"]
  , testCase "general e12" $ predecessorEdges g2 "e12" @?= ["e11"]
  , testCase "general e13" $ predecessorEdges g2 "e13" @?= ["e11"]
  , testCase "general e14" $ predecessorEdges g2 "e14" @?= ["e13"]
  , testCase "general e15" $ predecessorEdges g2 "e15" @?= ["e2"]
  ]

uPre :: TestTree
uPre = testGroup
  "Unit tests for preE"
  [ testCase "general e5" $ preE g2 "Or1" "e2" @?= ["e0", "e1", "e15"]
  , testCase "general e5"
  $   preE g2 "Or2" "e5"
  @?= ["e0", "e1", "e15", "e2", "e4"]
  , testCase "general e9"
  $   preE g2 "Or2" "e9"
  @?= ["e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"]
  , testCase "general e10" $ preE g2 "Or2" "e10" @?= []
  , testCase "general e11" $ preE g2 "Or2" "e11" @?= ["e10"]
  , testCase "general e12" $ preE g2 "Or2" "e12" @?= ["e10", "e11"]
  --
  , testCase "with communication e5"
  $   preE g3 "Or1" "e2"
  @?= ["e0", "e1", "e15"]
  , testCase "with communication e5"
  $   preE g3 "Or2" "e5"
  @?= ["e0", "e1", "e15", "e2", "e4"]
  , testCase "with communication e9"
  $   preE g3 "Or2" "e9"
  @?= ["e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"]
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
  attached
  []
  (fromList [])
  (fromList [])
  (fromList [])
 where
  catN = fromList
    [ ("Process" , Process)
    , ("Start"   , NoneStartEvent)
    , ("SplitAnd", AndGateway)
    , ("T1a"     , AbstractTask)
    , ("T2a"     , AbstractTask)
    , ("T1b"     , AbstractTask)
    , ( "T2b"    , AbstractTask)
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
  name     = fromList []
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]
  attached = fromList []

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
  attached
  []
  (fromList [])
  (fromList [])
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
  name     = fromList []
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]
  attached = fromList []

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
  attached
  []
  (fromList [])
  (fromList [])
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
  name     = fromList []
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]
  attached = fromList []

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
  attached
  []
  (fromList [])
  (fromList [])
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
  name     = fromList []
  containN = fromList [("Process", [])]
  containE = fromList [("Process", [])]
  attached = fromList []

g0e1 :: BpmnGraph
g0e1 = mkGraph
  "g0e1"
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
  ["message"]
  (fromList [("m", "message")])
  (fromList [])
  (fromList [])
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
    [("a", "NSE1"), ("b", "ST1"), ("c", "NSE2"), ("d", "RT2"), ("m", "NSE1")]
  target = fromList
    [("a", "ST1"), ("b", "NEE1"), ("c", "RT2"), ("d", "NEE2"), ("m", "RT2")]
  name     = fromList []
  containN = fromList
    [("Sender", ["NSE1", "ST1", "NEE1"]), ("Receiver", ["NSE2", "RT2", "NEE2"])]
  containE = fromList [("Sender", ["a", "b"]), ("Receiver", ["c", "d"])]
  attached = fromList []

g0e2 :: BpmnGraph
g0e2 = mkGraph
  "g0e2"
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
  ["message"]
  (fromList [("m", "message")])
  (fromList [])
  (fromList [])
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
    [("a", "ST1"), ("b", "NEE1"), ("c", "RT2"), ("d", "NEE2"), ("m", "NEE2")]
  name     = fromList []
  containN = fromList
    [("Sender", ["NSE1", "ST1", "NEE1"]), ("Receiver", ["NSE2", "RT2", "NEE2"])]
  containE = fromList [("Sender", ["a", "b"]), ("Receiver", ["c", "d"])]
  attached = fromList []

g2 :: BpmnGraph
g2 = mkGraph
  "g2"
  [ "Process"
  , "NSE"
  , "Xor0"
  , "AT1"
  , "Or1"
  , "Xor1"
  , "AT2"
  , "Xor2"
  , "AT3"
  , "Or2"
  , "AT4"
  , "Xor3"
  , "AT5"
  , "NEE"
  ]
  [ "e0"
  , "e1"
  , "e2"
  , "e3"
  , "e4"
  , "e5"
  , "e6"
  , "e7"
  , "e8"
  , "e9"
  , "e10"
  , "e11"
  , "e12"
  , "e13"
  , "e14"
  , "e15"
  ]
  catN
  catE
  source
  target
  (fromList [])
  containN
  containE
  attached
  []
  (fromList [])
  (fromList [])
  (fromList [])
 where
  catN = fromList
    [ ("Process", Process)
    , ("NSE"    , NoneStartEvent)
    , ("AT1"    , AbstractTask)
    , ("Xor0"   , XorGateway)
    , ("Or1"    , OrGateway)
    , ("Xor1"   , XorGateway)
    , ("AT2"    , AbstractTask)
    , ("Xor2"   , XorGateway)
    , ("AT3"    , AbstractTask)
    , ("Or2"    , OrGateway)
    , ("AT4"    , AbstractTask)
    , ("Xor3"   , XorGateway)
    , ("AT5"    , AbstractTask)
    , ("NEE"    , NoneEndEvent)
    ]
  catE = fromList
    [ ("e0" , NormalSequenceFlow)
    , ("e1" , NormalSequenceFlow)
    , ("e2" , NormalSequenceFlow)
    , ("e3" , ConditionalSequenceFlow)
    , ("e4" , ConditionalSequenceFlow)
    , ("e5" , NormalSequenceFlow)
    , ("e6" , NormalSequenceFlow)
    , ("e7" , NormalSequenceFlow)
    , ("e8" , DefaultSequenceFlow)
    , ("e9" , ConditionalSequenceFlow)
    , ("e10", NormalSequenceFlow)
    , ("e11", NormalSequenceFlow)
    , ("e12", DefaultSequenceFlow)
    , ("e13", ConditionalSequenceFlow)
    , ("e14", NormalSequenceFlow)
    , ("e15", DefaultSequenceFlow)
    ]
  source = fromList
    [ ("e0" , "NSE")
    , ("e1" , "Xor0")
    , ("e2" , "AT1")
    , ("e3" , "Or1")
    , ("e4" , "Or1")
    , ("e5" , "AT3")
    , ("e6" , "Xor1")
    , ("e7" , "AT2")
    , ("e8" , "Xor2")
    , ("e9" , "Xor2")
    , ("e10", "Or2")
    , ("e11", "AT4")
    , ("e12", "Xor3")
    , ("e13", "Xor3")
    , ("e14", "AT5")
    , ("e15", "Or1")
    ]
  target = fromList
    [ ("e0" , "Xor0")
    , ("e1" , "AT1")
    , ("e2" , "Or1")
    , ("e3" , "Xor1")
    , ("e4" , "AT3")
    , ("e5" , "Or2")
    , ("e6" , "AT2")
    , ("e7" , "Xor2")
    , ("e8" , "Xor1")
    , ("e9" , "Or2")
    , ("e10", "AT4")
    , ("e11", "Xor3")
    , ("e12", "Or2")
    , ("e13", "AT5")
    , ("e14", "NEE")
    , ("e15", "Xor0")
    ]
  containN = fromList
    [ ( "Process"
      , [ "NSE"
        , "AT1"
        , "Xor0"
        , "Or1"
        , "Xor1"
        , "AT2"
        , "Xor2"
        , "AT3"
        , "Or2"
        , "AT4"
        , "Xor3"
        , "AT5"
        , "NEE"
        ]
      )
    ]
  containE = fromList
    [ ( "Process"
      , [ "e0"
        , "e1"
        , "e2"
        , "e3"
        , "e4"
        , "e5"
        , "e6"
        , "e7"
        , "e8"
        , "e9"
        , "e10"
        , "e11"
        , "e12"
        , "e13"
        , "e14"
        , "e15"
        ]
      )
    ]
  attached = fromList []

g3 :: BpmnGraph
g3 = mkGraph
  "g3"
  [ "Process"
  , "NSE"
  , "Xor0"
  , "AT1"
  , "Or1"
  , "Xor1"
  , "AT2"
  , "Xor2"
  , "RT3"
  , "Or2"
  , "AT4"
  , "Xor3"
  , "AT5"
  , "NEE"
  , "Sender"
  , "NSE2"
  , "ST1"
  , "NEE2"
  ]
  [ "e0"
  , "e1"
  , "e2"
  , "e3"
  , "e4"
  , "e5"
  , "e6"
  , "e7"
  , "e8"
  , "e9"
  , "e10"
  , "e11"
  , "e12"
  , "e13"
  , "e14"
  , "e15"
  , "e16"
  , "e17"
  , "mf1"
  ]
  catN
  catE
  source
  target
  (fromList [])
  containN
  containE
  attached
  ["message"]
  (fromList [("mf1", "message")])
  (fromList [])
  (fromList [])
 where
  catN = fromList
    [ ("Process", Process)
    , ("NSE"    , NoneStartEvent)
    , ("AT1"    , AbstractTask)
    , ("Xor0"   , XorGateway)
    , ("Or1"    , OrGateway)
    , ("Xor1"   , XorGateway)
    , ("AT2"    , AbstractTask)
    , ("Xor2"   , XorGateway)
    , ("RT3"    , ReceiveTask)
    , ("Or2"    , OrGateway)
    , ("AT4"    , AbstractTask)
    , ("Xor3"   , XorGateway)
    , ("AT5"    , AbstractTask)
    , ("NEE"    , NoneEndEvent)
    , ("Sender" , Process)
    , ("NSE2"   , NoneStartEvent)
    , ("ST1"    , SendTask)
    , ("NEE2"   , NoneEndEvent)
    ]
  catE = fromList
    [ ("e0" , NormalSequenceFlow)
    , ("e1" , NormalSequenceFlow)
    , ("e2" , NormalSequenceFlow)
    , ("e3" , ConditionalSequenceFlow)
    , ("e4" , ConditionalSequenceFlow)
    , ("e5" , NormalSequenceFlow)
    , ("e6" , NormalSequenceFlow)
    , ("e7" , NormalSequenceFlow)
    , ("e8" , DefaultSequenceFlow)
    , ("e9" , ConditionalSequenceFlow)
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
    [ ("e0" , "NSE")
    , ("e1" , "Xor0")
    , ("e2" , "AT1")
    , ("e3" , "Or1")
    , ("e4" , "Or1")
    , ("e5" , "RT3")
    , ("e6" , "Xor1")
    , ("e7" , "AT2")
    , ("e8" , "Xor2")
    , ("e9" , "Xor2")
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
    [ ("e0" , "Xor0")
    , ("e1" , "AT1")
    , ("e2" , "Or1")
    , ("e3" , "Xor1")
    , ("e4" , "RT3")
    , ("e5" , "Or2")
    , ("e6" , "AT2")
    , ("e7" , "Xor2")
    , ("e8" , "Xor1")
    , ("e9" , "Or2")
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
    [ ( "Process"
      , [ "NSE"
        , "AT1"
        , "Xor0"
        , "Or1"
        , "Xor1"
        , "AT2"
        , "Xor2"
        , "AT3"
        , "Or2"
        , "AT4"
        , "Xor3"
        , "AT5"
        , "NEE"
        ]
      )
    , ("Sender", ["NSE2", "ST1", "NEE2"])
    ]
  containE = fromList
    [ ( "Process"
      , [ "e0"
        , "e1"
        , "e2"
        , "e3"
        , "e4"
        , "e5"
        , "e6"
        , "e7"
        , "e8"
        , "e9"
        , "e10"
        , "e11"
        , "e12"
        , "e13"
        , "e14"
        , "e15"
        ]
      )
    , ("Sender", ["e16", "e17"])
    ]
  attached = fromList []
