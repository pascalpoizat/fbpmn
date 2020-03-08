{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Alloy.IO.Alloy where

import qualified Data.Text         as T
import           Fbpmn.Helper
import           Fbpmn.BpmnGraph.Model
import           NeatInterpolation (text)
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict   ((!?), foldrWithKey)

{-|
Write a BPMN Graph to an Alloy file.
-}
writeToAlloy :: FilePath -> Maybe a -> BpmnGraph -> IO ()
writeToAlloy p _ = writeFile p . toString . encodeBpmnGraphToAlloy

{-|
Transform a BPMN Graph to an Alloy specification.
-}
encodeBpmnGraphToAlloy :: BpmnGraph -> Text
encodeBpmnGraphToAlloy g =
  unlines
    $   [ encodeBpmnGraphHeaderToAlloy          -- header
        , encodeBpmnGraphFooterToAlloy          -- footer
        ]
    <*> [g]

encodeBpmnGraphHeaderToAlloy :: BpmnGraph -> Text
encodeBpmnGraphHeaderToAlloy g =
  [text|
  ---------------- MODULE $n ----------------
  module $n

  |]
  where
    n = name g

encodeBpmnGraphFooterToAlloy :: BpmnGraph -> Text
encodeBpmnGraphFooterToAlloy g =
  [text|
  ---------------- END MODULE $n ------------
  |]
  where
    n = name g
