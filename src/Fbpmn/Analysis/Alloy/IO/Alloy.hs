{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Alloy.IO.Alloy where

import           Fbpmn.BpmnGraph.Model
import           Fbpmn.Analysis.Alloy.Model
import           NeatInterpolation              ( text )
import           Data.Map.Strict                ( (!?) )
import           Data.Time.Format.ISO8601
import           Data.Time.LocalTime
import           Data.Time.Calendar
import           Data.Time.Clock
import           Data.Time.Clock.POSIX
import           Control.Monad
import           Data.Attoparsec.Text           ( Parser
                                                , parse
                                                , decimal
                                                , string
                                                , option
                                                , maybeResult
                                                )

-- Time-related elements
--
-- TimeDate
--  format: yyyy-mm-ddThh:mm:ssZ
--  constraints:
--    - all parts must be given (can be 0)
-- TimeDuration
--  format: PyYmmMdDThHmMsS
--  constraints:
--    - y and mm must be O or not given,
--    - sS must be given (can be 0)
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
-- [X] TBE non interrupting + timedate
-- [X] TBE interrupting + duration
-- [X] TBE non interrupting + duration
-- [ ] TBE non interrupting + cycle duration
-- [ ] TBE non interrupting + infinite cycle duration
-- [ ] TBE non interrupting + cycle start/duration
-- [ ] TBE non interrupting + infinite cycle start/duration
-- [ ] TBE non interrupting + cycle duration/end
-- [ ] TBE non interrupting + infinite cycle duration/end
--

{-|
Helper for acting based on node types
-}
infixr 0 |>
(|>) :: Bool -> a -> Maybe a
True  |> x = Just x
False |> _ = Nothing

{-|
Helpers for node types
-}
nTSE :: NodeType
nTSE = TimerStartEvent
nTICE :: NodeType
nTICE = TimerIntermediateEvent
nTBE :: NodeType
nTBE = TimerBoundaryEvent
nMBE :: NodeType
nMBE = MessageBoundaryEvent
nP :: NodeType
nP = Process
nSP :: NodeType
nSP = SubProcess

{-|
Subtypes for cycles
-}
data TimeCycleSubtype = CycleStart | CycleEnd | CycleDuration
  deriving (Show)

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
        -- , encodeBpmnGraphFooterToAlloy vs
        ]
    <*> [g]
--  where
--   vs =
--     [ AlloyVerification Check Safety             15
--     , AlloyVerification Check SimpleTermination  9
--     , AlloyVerification Check CorrectTermination 9
--     , AlloyVerification Run   Safety             11
--     ]

encodeBpmnGraphHeaderToAlloy :: BpmnGraph -> Text
encodeBpmnGraphHeaderToAlloy g = [text|
  module $mname

  open PWSSyntax
  open PWSProp

  |]
  where mname = name g

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
messageToAlloy m = [text|one sig $mname extends Message {}|]
  where mname = toText m

nodeToAlloy :: BpmnGraph -> Node -> Text
nodeToAlloy g n = [text|
  $tinfo
  one sig $nname extends $ntype {} {$values}
  |]
 where
  nname = toText n
  ntype = maybe "" nodeTypeToAlloy (catN g !? n)
  values =
    unlines
      .   catMaybes
      $   [containsToAlloy g, teInfoToAlloy g, beInfoToAlloy g]
      <*> [n]
  tinfo = fromMaybe "" $ timeInfoToAlloy g n

teInfoToAlloy :: BpmnGraph -> Node -> Maybe Text
teInfoToAlloy g n =
  (n `elem` nodesTs g [nTSE, nTICE, nTBE]) |> [text|mode = $tmode|]
  where tmode = toText n <> "time"

containsToAlloy :: BpmnGraph -> Node -> Maybe Text
containsToAlloy g n =
  (n `elem` nodesTs g [nSP, nP]) |> [text|contains = $nces|]
  where nces = toText $ intercalate " + " $ concat (containN g !? n)

beInfoToAlloy :: BpmnGraph -> Node -> Maybe Text
beInfoToAlloy g n = join $ (n `elem` nodesTs g [nMBE, nTBE]) |> do
  ncontainer    <- toText <$> attached g !? n
  ninterrupting <- boolToAlloy <$> isInterrupt g !? n
  Just [text|attachedTo = $ncontainer
            interrupting = $ninterrupting|]

timeInfoToAlloy :: BpmnGraph -> Node -> Maybe Text
timeInfoToAlloy g n =
  join
    $  (n `elem` nodesTs g [nTSE, nTICE, nTBE])
    |> (timeInformation g !? n >>= timerEventDefinitionToAlloy n)

-- evolutions:
-- - add timezones
-- - take into account a parametric time start (not 1970-01-01T00:00:00)
--    note: this will require supporting negative numbers
-- - signal errors at parsing or transforming
--
timerEventDefinitionToAlloy :: Node -> TimerEventDefinition -> Maybe Text
timerEventDefinitionToAlloy n (TimerEventDefinition (Just tdt) (Just tdv)) =
  timerEventDefinitionToAlloy' tdt (toText tdv) (toText n)
timerEventDefinitionToAlloy _ (TimerEventDefinition _ _) = Nothing

timerEventDefinitionToAlloy' :: TimerDefinitionType
                             -> Text
                             -> Text
                             -> Maybe Text
timerEventDefinitionToAlloy' TimeDate val n = do
  let parsed = parse parseDateTime val
  res <- maybeResult parsed
  let vval = dateToAlloy res
  let ni   = n <> "time"
  Just [text|one sig $ni extends Date {} {
    date = $vval
  }|]
timerEventDefinitionToAlloy' TimeDuration val n = do
  let parsed = parse parseDuration val
  res <- maybeResult parsed
  let vval = durationToAlloy res
  let ni   = n <> "time"
  Just [text|one sig $ni extends Duration {} {
    duration = $vval
  }|]
timerEventDefinitionToAlloy' TimeCycle val n = do
  let parsed =
        [flip parse val]
          <*> [parseCycleStart, parseCycleEnd, parseCycleDuration]
  ti@(dtype, _, _, _) <- msum $ maybeResult <$> parsed
  ncontents           <- timerEventDefinitionToAlloy'' ti
  let ntype = show dtype
  let ni    = n <> "time"
  Just [text|one sig $ni extends $ntype {} {
    $ncontents
  }|]

timerEventDefinitionToAlloy'' :: ( TimeCycleSubtype
                                 , Maybe Integer
                                 , CalendarDiffTime
                                 , Maybe UTCTime
                                 )
                              -> Maybe Text
timerEventDefinitionToAlloy'' (CycleStart, nb, dur, dat) = do
  nbase <- timerEventDefinitionToAlloy'' (CycleDuration, nb, dur, dat)
  ndat  <- dateToAlloy <$> dat
  Just [text|$nbase
    startdate = $ndat|]
timerEventDefinitionToAlloy'' (CycleEnd, nb, dur, dat) = do
  nbase <- timerEventDefinitionToAlloy'' (CycleDuration, nb, dur, dat)
  ndat  <- dateToAlloy <$> dat
  Just [text|$nbase
    enddate = $ndat|]
timerEventDefinitionToAlloy'' (CycleDuration, nb, dur, _) = do
  nnb <- show <$> nb
  let vval = durationToAlloy dur
  Just [text|repetition = $nnb
      duration = $vval|]

{-   let parsed1 = parse parseCycleStart val
      parsed2 = parse parseCycleEnd val
      parsed3 = parse parseCycleDuration val
      results = 
    case (maybeResult parsed1, maybeResult parsed2, maybeResult parsed3)
      of
              (Just (nb, date, dur), _, _) -> Just
                ( "CycleDurationStart"
                , show $ fromMaybe 0 nb
                , show $ durationToAlloy dur
                , show $ dateToAlloy date
                )
              (Nothing, Just (nb, dur, date), _) -> Just
                ( "CycleDurationEnd"
                , show $ fromMaybe 0 nb
                , show $ durationToAlloy dur
                , show $ dateToAlloy date
                )
              (Nothing, Nothing, Just (nb, dur)) -> Just
                ( "CycleDuration"
                , show $ fromMaybe 0 nb
                , show $ durationToAlloy dur
                , undefAlloy
                )
              _ -> Just ("ERROR", msg1, msg2, msg3)
               where
                msg1 = case eitherResult parsed1 of
                  Right _ -> ""
                  Left  m -> toText m
                msg2 = case eitherResult parsed2 of
                  Right _ -> ""
                  Left  m -> toText m
                msg3 = case eitherResult parsed3 of
                  Right _ -> ""
                  Left  m -> toText m
 -}
iso8601DateTimeParser :: String -> Maybe UTCTime
iso8601DateTimeParser = formatParseM iso8601Format

iso8601DurationParser :: String -> Maybe CalendarDiffTime
iso8601DurationParser = formatParseM iso8601Format

iso8601DateTimeFormat :: Format UTCTime
iso8601DateTimeFormat = utcTimeFormat iso8601Format iso8601Format

iso8601DurationFormat :: Format CalendarDiffTime
iso8601DurationFormat = durationTimeFormat

iso8601CycleStartParser :: String -> Maybe (Int, UTCTime, CalendarDiffTime)
iso8601CycleStartParser = formatParseM
  (recurringIntervalFormat iso8601DateTimeFormat iso8601DurationFormat)

iso8601CycleEndParser :: String -> Maybe (Int, CalendarDiffTime, UTCTime)
iso8601CycleEndParser = formatParseM
  (recurringIntervalFormat iso8601DurationFormat iso8601DateTimeFormat)

-- from Text.Parsec.Combinator
optionMaybe :: (Alternative f, Monad f) => f a -> f (Maybe a)
optionMaybe p = option Nothing (liftM Just p)

parseInteger :: Parser Integer
parseInteger = decimal

parseTerminal :: Text -> Parser ()
parseTerminal sep = do
  _ <- string sep
  return ()

parseValSep :: Text -> Parser Integer
parseValSep sep = do
  val <- parseInteger
  _   <- parseTerminal sep
  return val

parseValSepOpt :: Text -> Parser Integer
parseValSepOpt sep = option 0 (parseValSep sep)

-- R(n)/DateTime/Duration
parseCycleStart :: Parser
                     ( TimeCycleSubtype
                     , Maybe Integer
                     , CalendarDiffTime
                     , Maybe UTCTime
                     )
parseCycleStart = do
  _   <- parseTerminal "R"
  n   <- optionMaybe parseInteger
  _   <- parseTerminal "/"
  dt  <- parseDateTime
  _   <- parseTerminal "/"
  dur <- parseDuration
  return (CycleStart, n, dur, Just dt)

-- R(n)/Duration/DateTime
parseCycleEnd :: Parser
                   ( TimeCycleSubtype
                   , Maybe Integer
                   , CalendarDiffTime
                   , Maybe UTCTime
                   )
parseCycleEnd = do
  _   <- parseTerminal "R"
  n   <- optionMaybe parseInteger
  _   <- parseTerminal "/"
  dur <- parseDuration
  _   <- parseTerminal "/"
  dt  <- parseDateTime
  return (CycleEnd, n, dur, Just dt)

-- R(n)/Duration
parseCycleDuration :: Parser
                        ( TimeCycleSubtype
                        , Maybe Integer
                        , CalendarDiffTime
                        , Maybe UTCTime
                        )
parseCycleDuration = do
  _ <- parseTerminal "R"
  n <- optionMaybe parseInteger
  _ <- parseTerminal "/"
  c <- parseDuration
  return (CycleDuration, n, c, Nothing)

-- YYYY-MM-DDTHH:MM:SSZ
parseDateTime :: Parser (UTCTime)
parseDateTime = do
  y  <- parseInteger
  _  <- parseTerminal "-"
  m  <- parseInteger
  _  <- parseTerminal "-"
  d  <- parseInteger
  _  <- parseTerminal "T"
  h  <- parseInteger
  _  <- parseTerminal ":"
  mn <- parseInteger
  _  <- parseTerminal ":"
  s  <- parseInteger
  _  <- parseTerminal "Z"
  let day  = fromGregorian y (fromInteger m) (fromInteger d)
  let time = secondsToDiffTime $ (h * 3600) + (mn * 60) + s
  return $ UTCTime day time

-- PyYmMdDThHmMsS
parseDuration :: Parser (CalendarDiffTime)
parseDuration = do
  _          <- parseTerminal "P"
  _          <- parseValSepOpt "Y"
  m          <- parseValSepOpt "M"
  d          <- parseValSepOpt "D"
  (h, mn, s) <- option (0, 0, 0) parseHMS
  return (CalendarDiffTime m $ computeDiff d h mn s)

-- ThHmMsS
parseHMS :: Parser (Integer, Integer, Integer)
parseHMS = do
  _ <- parseTerminal "T"
  h <- parseValSepOpt "H"
  m <- parseValSepOpt "M"
  s <- parseValSepOpt "S"
  return (h, m, s)

computeDiff :: Integer -> Integer -> Integer -> Integer -> NominalDiffTime
computeDiff d h m s = secondsToNominalDiffTime picos
 where
  seconds = (d * 24 * 3600) + (h * 3600) + (m * 60) + s
  picos   = fromInteger seconds

undefAlloy :: Text
undefAlloy = "0"

boolToAlloy :: Bool -> Text
boolToAlloy True  = "True"
boolToAlloy False = "False"

edgeToAlloy :: BpmnGraph -> Edge -> Text
edgeToAlloy g e = [text|one sig $ename extends $etype {} {$values}|]
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

dateToAlloy :: UTCTime -> Text
dateToAlloy = timeToAlloy utcTimeToPOSIXSeconds

durationToAlloy :: CalendarDiffTime -> Text
durationToAlloy = timeToAlloy ctTime

timeToAlloy :: (a -> NominalDiffTime) -> a -> Text
timeToAlloy f = show . truncate . nominalDiffTimeToSeconds . f
