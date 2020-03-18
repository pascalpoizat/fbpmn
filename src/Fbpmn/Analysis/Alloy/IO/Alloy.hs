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

import           Data.Time.Format.ISO8601
import           Data.Time.Format
import           Data.Time.LocalTime
import           Data.Time.Clock
import           Data.Time.Clock.POSIX

-- Time-related elements
--
-- TimeDate format = yyyy-mm-ddThh:mm:ssZ (MUST BE UTC)
--  all parts must be given (even if 0)
-- TimeDuration format = PyYmmMdDThHmMsS
--  y and mm must be O or not given
-- TimeCycle format = several choices (6):
-- - R(n)?/duration
-- - R(n)?/timedate/duration
-- - R(n)?/duration/timedate
--
-- NO VERIFICATION DONE IN THE BPMN PARSING NOR HERE
--
-- [X] TSE + timedate
-- [X] TICE + timedate
-- [X] TICE + duration
-- [X] TBE interrupting + timedate
-- [X] TBE interrupting + duration
-- [ ] TBE non interrupting + cycle (6 formats for the cycle)
--

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
    $   [ encodeBpmnGraphHeaderToAlloy
        , encodeMessages
        , encodeNodes
        , encodeEdges
        , encodeBpmnGraphFooterToAlloy vs
        ]
    <*> [g]
 where
  vs =
    [ AlloyVerification Check Safety             15
    , AlloyVerification Check SimpleTermination  9
    , AlloyVerification Check CorrectTermination 9
    , AlloyVerification Run   Safety             11
    ]

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
    Run   -> "run"
    Check -> "check"
  tprop = case property v of
    Safety             -> "Safe"
    SimpleTermination  -> "SimpleTermination"
    CorrectTermination -> "CorrectTermination"
  tnb = show $ nb v

encodeMessages :: BpmnGraph -> Text
encodeMessages g = unlines $ messageToAlloy <$> messages g

encodeNodes :: BpmnGraph -> Text
encodeNodes g = unlines $ nodeToAlloy g <$> nodes g

encodeEdges :: BpmnGraph -> Text
encodeEdges g = unlines $ edgeToAlloy g <$> edges g

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

messageToAlloy :: Message -> Text
messageToAlloy m = [text|one sig $mname extends MessageKind {}|]
  where mname = toText m

nodeToAlloy :: BpmnGraph -> Node -> Text
nodeToAlloy g n = [text|one sig $nname extends $ntype {$values}|]
 where
  nname  = toText n
  ntype  = maybe "" nodeTypeToAlloy (catN g !? n)
  values = unlines . catMaybes $ [containsToAlloy g, timeInfoToAlloy g] <*> [n]

containsToAlloy :: BpmnGraph -> Node -> Maybe Text
containsToAlloy g n = if n `elem` nodesTs g [SubProcess, Process]
  then Just [text|
    contains = $nces|]
  else Nothing
  where nces = toText $ intercalate " + " $ concat (containN g !? n)

timeInfoToAlloy :: BpmnGraph -> Node -> Maybe Text
timeInfoToAlloy g n =
  if n `elem` nodesTs
       g
       [TimerStartEvent, TimerIntermediateEvent, TimerBoundaryEvent]
    then case timerEventDefinitionToAlloy =<< timeInformation g !? n of
      Just (mode, repetition, duration, date) -> Just [text|
        mode = $mode
        repetition = $repetition
        duration = $duration
        date = $date
        |]
      Nothing -> Nothing
    else Nothing

-- evolutions:
-- - add timezones
-- - take into account a parametric time start (not 1970-01-01T00:00:00)
-- - signal errors at parsing or transforming
--
timerEventDefinitionToAlloy :: TimerEventDefinition
                            -> Maybe (Text, Text, Text, Text)
timerEventDefinitionToAlloy (TimerEventDefinition (Just tdt) (Just tdv)) =
  case tdt of
    TimeDate -> do
      parsed <- formatParseM iso8601Format tdv
      let nuot = nominalDiffTimeToSeconds . utcTimeToPOSIXSeconds $ parsed
      Just ("Date", undefAlloy, undefAlloy, show nuot)
    TimeDuration -> do
      parsed <- formatParseM iso8601Format tdv
      nuot <- case ctMonths parsed of
        -- if we have months then year/month has been used in duration: error
        0 -> Just . nominalDiffTimeToSeconds . ctTime $ parsed
        _ -> Nothing
      Just ("Duration", undefAlloy, show nuot, undefAlloy)
    TimeCycle ->
      Just ("Cycle", undefAlloy, undefAlloy, undefAlloy) -- TODO:
timerEventDefinitionToAlloy _ = Nothing

undefAlloy :: Text
undefAlloy = "0"

edgeToAlloy :: BpmnGraph -> Edge -> Text
edgeToAlloy g e = [text|one sig $ename extends $etype {$values}|]
 where
  ename = toText e
  etype = maybe "" edgeTypeToAlloy (catE g !? e)
  values =
    unlines . catMaybes $ [flowToAlloy g, messageInformationToAlloy g] <*> [e]

flowToAlloy :: BpmnGraph -> Edge -> Maybe Text
flowToAlloy g e = case (esource, etarget) of
  (Just n1, Just n2) -> Just [text|
      source = $sn1
      target = $sn2
    |]
   where
    sn1 = toText n1
    sn2 = toText n2
  _ -> Nothing
 where
  esource = sourceE g !? e
  etarget = targetE g !? e

messageInformationToAlloy :: BpmnGraph -> Edge -> Maybe Text
messageInformationToAlloy g e = case messageE g !? e of
  Just m  -> Just [text|message = $sm|] where sm = toText m
  Nothing -> Nothing
