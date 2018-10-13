import           Test.Tasty
import           Test.Tasty.HUnit
-- import           Test.Tasty.QuickCheck as QC
-- import           Test.Tasty.SmallCheck as SC
import           Test.Tasty.Runners.Html

import Fbpmn

main :: IO ()
main = defaultMainWithIngredients (htmlRunner : defaultIngredients) test

test :: TestTree
test = testGroup "Tests" [mainTests]

mainTests :: TestTree
mainTests = testGroup "Main tests" [unittests]

unittests :: TestTree
unittests = testGroup "Unit tests" [uNodesT, uEdgesT, uInN, uOutN]

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
  @?= ["e1","es+a","es+b","e2a","e2b","ej+a","ej+b","e3"]
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
-- g1
--
-- NSE -> + {T1, T2} + -> NEE
--
g1 :: BpmnGraph
g1 = BpmnGraph
  ["Start", "SplitAnd", "T1a", "T1b", "T2a", "T2b", "JoinAnd", "End"]
  ["e1", "es+a", "es+b", "e2a", "e2b", "ej+a", "ej+b", "e3"]
  catN
  catE
  source
  target
 where
  catN n = case n of
    "Start"    -> Just NoneStartEvent
    "SplitAnd" -> Just AndGateway
    "T1a"      -> Just AbstractTask
    "T2a"      -> Just AbstractTask
    "T1b"      -> Just AbstractTask
    "T2b"      -> Just AbstractTask
    "JoinAnd"  -> Just AndGateway
    "End"      -> Just NoneEndEvent
    _          -> Nothing
  catE e = case e of
    "e1"   -> Just NormalSequenceFlow
    "es+a" -> Just NormalSequenceFlow
    "es+b" -> Just NormalSequenceFlow
    "e2a"  -> Just NormalSequenceFlow
    "e2b"  -> Just NormalSequenceFlow
    "ej+a" -> Just NormalSequenceFlow
    "ej+b" -> Just NormalSequenceFlow
    "e3"   -> Just NormalSequenceFlow
    _      -> Nothing
  source e = case e of
    "e1"   -> Just "Start"
    "es+a" -> Just "SplitAnd"
    "es+b" -> Just "SplitAnd"
    "e2a"  -> Just "T1a"
    "e2b"  -> Just "T1b"
    "ej+a" -> Just "T2a"
    "ej+b" -> Just "T2b"
    "e3"   -> Just "JoinAnd"
    _      -> Nothing
  target e = case e of
    "e1"   -> Just "SplitAnd"
    "es+a" -> Just "T1a"
    "es+b" -> Just "T1b"
    "e2a"  -> Just "T2a"
    "e2b"  -> Just "T2b"
    "ej+a" -> Just "JoinAnd"
    "ej+b" -> Just "JoinAnd"
    "e3"   -> Just "End"
    _      -> Nothing

