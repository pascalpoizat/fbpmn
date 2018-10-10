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
unittests = testGroup "Unit tests" [uDummy]

uDummy :: TestTree
uDummy = testGroup "Unit tests for add"
  [
    testCase "add 0/0" $
    add 0 0 @?= 0
  , testCase "add 0/n" $
    add 0 2 @?= 2
  , testCase "add n/m" $
    add 2 3 @?= 5
  ]
