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
        , encodeNodes                           -- experimental
        , encodeTimerEventDefinitions           -- experimental
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

encodeNodes :: BpmnGraph -> Text
encodeNodes g = [text|
  $sn
  |]
  where
    sn = unlines $ nodeToAlloy <$> ns
    ns = nodes g
    nodeToAlloy n = [text|$ssn :: $tn|]
      where
        ssn = show n
        tn = maybe "type not known" show $ catN g !? n

encodeTimerEventDefinitions :: BpmnGraph -> Text
encodeTimerEventDefinitions g = [text|
    TimerEventDefinitions ==
    $stes
  |]
 where
  stes = unlines $ teToAlloy <$> tes
  tes  = nodesTs g [TimerStartEvent, TimerIntermediateEvent, TimerBoundaryEvent]
  teToAlloy e = case timeInformation g !? e of
    Just (TimerEventDefinition (Just ttype) tval) ->
      [text|$side :: $sttype -> $stval|]
     where
      side   = show e
      sttype = case ttype of
        TimeDate     -> "date"
        TimeDuration -> "duration"
        TimeCycle    -> "cycle"
      stval = maybe "value not set" show tval
    _ -> [text|$side = type not set|] where side = show e

