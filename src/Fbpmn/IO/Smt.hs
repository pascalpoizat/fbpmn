module Fbpmn.IO.Smt where

import           Fbpmn.Model

{-|
Write a BPMN Graph to an SMT file.
-}
writeToSMT :: FilePath -> BpmnGraph -> IO ()
writeToSMT p = writeFile p . encodeBpmnGraphToSmt

{-|
Transform a BPMN Graph to an SMT description.

The solution is to use a model to text transformation.
TODO: In terms of typing, it would be better to use a model to model transformation (first).
-}
encodeBpmnGraphToSmt :: BpmnGraph -> String
encodeBpmnGraphToSmt g = unlines
  [ "; BPMN Graph encoded using fBPMN\n"
  , encodeBpmnGraphNodesToSmt g
  , "; end of encoding"
  ]

encodeBpmnGraphNodesToSmt :: BpmnGraph -> String
encodeBpmnGraphNodesToSmt g = "; Process node declarations\n"
  <> unlines (nodeToNodeDeclaration g <$> nodes g)
 where
  nodeToNodeDeclaration :: BpmnGraph -> Node -> String
  nodeToNodeDeclaration _ n = "(declare-fun " <> n <> " () (Array Int Int))"
