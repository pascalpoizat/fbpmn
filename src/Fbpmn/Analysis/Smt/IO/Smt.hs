module Fbpmn.Analysis.Smt.IO.Smt where

import           Fbpmn.BpmnGraph.Model

{-|
Write a BPMN Graph to an SMT file.
-}
writeToSMT :: FilePath -> BpmnGraph -> IO ()
writeToSMT p = writeFile p . toString . encodeBpmnGraphToSmt

{-|
Transform a BPMN Graph to an SMT description.

The solution is to use a model to text transformation.
TODO: In terms of typing, it would be better to use a model to model transformation (first).
-}
encodeBpmnGraphToSmt :: BpmnGraph -> Text
encodeBpmnGraphToSmt = encodeBpmnGraphNodesToSmt

encodeBpmnGraphNodesToSmt :: BpmnGraph -> Text
encodeBpmnGraphNodesToSmt g = unlines (nodeToNodeDeclaration <$> nodes g)
 where
  nodeToNodeDeclaration :: Node -> Text
  nodeToNodeDeclaration n = "(declare-fun " <> show n <> "() (Array Int Int))"

