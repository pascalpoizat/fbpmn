{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Alloy.IO.Alloy where

import qualified Data.Text                     as T
import           Fbpmn.Helper
import           Fbpmn.BpmnGraph.Model
import           Fbpmn.Analysis.Alloy.Model
import           NeatInterpolation              ( text )
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict                ( (!?)
                                                , foldrWithKey
                                                )

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
    $   [ encodeBpmnGraphHeaderToAlloy          --    
        , encodeNodes
        , encodeEdges
        , encodeBpmnGraphFooterToAlloy vs
        ]
    <*> [g]
    where
      vs = [ AlloyVerification Check Safety 15
           , AlloyVerification Check SimpleTermination 9
           , AlloyVerification Check CorrectTermination 9
           , AlloyVerification Run Safety 11]

encodeBpmnGraphHeaderToAlloy :: BpmnGraph -> Text
encodeBpmnGraphHeaderToAlloy _ = [text|
  open PWSSyntax
  open PWSProp

  |]

encodeBpmnGraphFooterToAlloy :: [AlloyVerification] -> BpmnGraph -> Text
encodeBpmnGraphFooterToAlloy vs _ = unlines $ verificationToAlloy <$> vs

verificationToAlloy :: AlloyVerification -> Text
verificationToAlloy v = [text|$tact {$tprop} for 0 but $tnb State|]
  where
    tact = case action v of
      Run -> "run"
      Check -> "check"
    tprop = case property v of
      Safety -> "Safe"
      SimpleTermination -> "SimpleTermination"
      CorrectTermination -> "CorrectTermination"
    tnb = show $ nb v

encodeNodes :: BpmnGraph -> Text
encodeNodes g = [text|
  $sns
  |]
 where
  sns = unlines $ nodeToAlloy <$> nodes g
  nodeToAlloy n = [text|
      one sig $nname extends $ntype {
        $ncontents
      }
      |]
   where
    nname = toText n
    ntype = maybe "" nodeTypeToAlloy (catN g !? n)
    ncontents = if n `elem` nodesTs g [SubProcess, Process]
      then [text|contains = $nces|]
      else ""
        where
          ces = concat $ containN g !? n
          nces = toText $ intercalate " + " ces  

encodeEdges :: BpmnGraph -> Text
encodeEdges g = [text|
  $ses
  |]
 where
  ses = unlines $ edgeToAlloy <$> edges g
  edgeToAlloy e = [text|
      one sig $ename extends $etype {
        $eflowinformation
      }
      |]
   where
    ename     = toText e
    etype     = maybe "" edgeTypeToAlloy (catE g !? e)
    esource   = sourceE g !? e
    etarget   = targetE g !? e
    eflowinformation = case (esource, etarget) of
      (Just n1, Just n2) -> [text|
              source = $sn1
              target = $sn2|]
       where
        sn1 = toText n1
        sn2 = toText n2
      _ -> ""

nodeTypeToAlloy :: NodeType -> Text
nodeTypeToAlloy AbstractTask                  = "AbstractTask"
-- start
nodeTypeToAlloy NoneStartEvent                = "NoneStartEvent"
-- end
nodeTypeToAlloy NoneEndEvent                  = "NoneEndEvent"
nodeTypeToAlloy TerminateEndEvent             = "TerminateEndEvent"
-- gateways
nodeTypeToAlloy XorGateway                    = "ExclusiveOr"
nodeTypeToAlloy OrGateway                     = "InclusiveOr"
nodeTypeToAlloy AndGateway                    = "Parallel"
nodeTypeToAlloy EventBasedGateway             = "EventBased"
-- structure
nodeTypeToAlloy SubProcess                    = "SubProcess"
nodeTypeToAlloy Process                       = "Process"
-- communication
nodeTypeToAlloy MessageStartEvent             = "MessageStartEvent"
nodeTypeToAlloy SendTask                      = "SendTask"
nodeTypeToAlloy ReceiveTask                   = "ReceiveTask"
nodeTypeToAlloy ThrowMessageIntermediateEvent = "ThrowMessageIntermediateEvent"
nodeTypeToAlloy CatchMessageIntermediateEvent = "CatchMessageIntermediateEvent"
nodeTypeToAlloy MessageBoundaryEvent          = "MessageBoundaryEvent"
nodeTypeToAlloy MessageEndEvent               = "MessageEndEvent"
-- time
nodeTypeToAlloy TimerStartEvent               = "TimerStartEvent"
nodeTypeToAlloy TimerIntermediateEvent        = "TimerIntermediateEvent"
nodeTypeToAlloy TimerBoundaryEvent            = "TimerBoundaryEvent"

edgeTypeToAlloy :: EdgeType -> Text
edgeTypeToAlloy NormalSequenceFlow      = "NormalSequentialFlow"
edgeTypeToAlloy ConditionalSequenceFlow = "ConditionalSequentialFlow"
edgeTypeToAlloy DefaultSequenceFlow     = "DefaultSequentialFlow"
edgeTypeToAlloy MessageFlow             = "MessageFlow"

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

