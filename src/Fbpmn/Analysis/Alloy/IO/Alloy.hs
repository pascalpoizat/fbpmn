{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Alloy.IO.Alloy where

import           Fbpmn.BpmnGraph.Model
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

--
-- Generic (may possibly be moved to a transformation library)
--

-- predicate (check if something is true for a in context c)
type Pred c a = c -> a -> Bool

-- type predicate (check if a is of a type in [t] in context c)
type TypePred c a t = [t] -> Pred c a

-- selector (get all a that are of a type in [t] in context c)
type Selector c a t = c -> [t] -> [a]

-- transformers (transform a a into a text in context c, may fail)
type Transformer c a = c -> a -> Maybe Text

-- transformer application (over an a)
apply :: Transformer c a -> c -> a -> Maybe Text
apply = ($)

-- transformer application (over a list of as)
applyN :: Transformer c a -> c -> [a] -> Maybe Text
applyN f c as = Just . unlines . catMaybes $ f c <$> as

-- constrain a transformer with a predicate
infixr 0 =>>
(=>>) :: Pred c a -> Transformer c a -> Transformer c a
s =>> t = \c a -> if s c a then t c a else Nothing

-- predicate wrt being of a type defined in the context
ofType :: (Eq a) => Selector c a t -> TypePred c a t
ofType sel ts c a = a `elem` sel c ts

--
-- BPMN Graph specific (may possibly be moved to the BPMNGraph library)
--

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

-- graph predicate
type GraphPred a = Pred BpmnGraph a

-- node predicate
type NodePredicate = GraphPred Node

-- edge predicate
type EdgePredicate = GraphPred Edge

-- node type predicate
type NodeTypePred = TypePred BpmnGraph Node NodeType

-- edge type predicate
type EdgeTypePred = TypePred BpmnGraph Edge EdgeType

-- graph transformers
type GraphTransformer a = Transformer BpmnGraph a

inNodeTypes :: NodeTypePred
inNodeTypes = ofType nodesTs

inEdgeTypes :: EdgeTypePred
inEdgeTypes = ofType edgesTs

isTimed :: NodePredicate
isTimed = inNodeTypes [nTSE, nTICE, nTBE]

isContainer :: NodePredicate
isContainer = inNodeTypes [nSP, nP]

isBoundaryEvent :: NodePredicate
isBoundaryEvent = inNodeTypes [nMBE, nTBE]

--
-- Alloy specific
--

-- sybtypes for cycles
data TimeCycleSubtype = CycleStart | CycleEnd | CycleDuration
  deriving (Show)

-- undefined value
genUndef :: Text
genUndef = "0"

-- boolean values
genBool :: GraphTransformer Bool
genBool _ True  = Just "True"
genBool _ False = Just "False"

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
    .   catMaybes
    $   [genHeader, genMessages, genNodes, genEdges]
    <*> [g]
    <*> [()]

genHeader :: GraphTransformer ()
genHeader g _ = Just [text|
  module $mname

  open PWSSyntax
  open PWSProp

  |]
  where mname = name g

genMessages :: GraphTransformer ()
genMessages g _ = applyN genMessage g $ messages g

genNodes :: GraphTransformer ()
genNodes g _ = applyN genNode g $ nodes g

genEdges :: GraphTransformer ()
genEdges g _ = applyN genEdge g $ edges g

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

genMessage :: GraphTransformer Message
genMessage _ m = Just [text|one sig $mname extends Message {}|]
  where mname = toText m

genNode :: GraphTransformer Node
genNode g n = Just [text|
  $tinfo
  one sig $nname extends $ntype {} {$values}
  |]
 where
  tinfo = fromMaybe "" $ apply genTimeDefinition g n
  nname = toText n
  ntype = maybe "" nodeTypeToAlloy (catN g !? n)
  values =
    unlines
      .   catMaybes
      $   [genContainment, genBoundaryInformation, genTimeReference]
      <*> [g]
      <*> [n]

genEdge :: GraphTransformer Edge
genEdge g e = Just [text|one sig $ename extends $etype {} {$values}|]
 where
  ename = toText e
  etype = maybe "" edgeTypeToAlloy (catE g !? e)
  values =
    unlines . catMaybes $ [flowToAlloy g, messageInformationToAlloy g] <*> [e]

genContainment :: GraphTransformer Node
genContainment = isContainer =>> f
 where
  f g n =
    let nces = toText $ intercalate " + " $ concat (containN g !? n)
    in  Just [text|contains = $nces|]

genBoundaryInformation :: GraphTransformer Node
genBoundaryInformation = isBoundaryEvent =>> f
 where
  f g n = do
    ncontainer    <- toText <$> attached g !? n
    interrupting  <- isInterrupt g !? n
    ninterrupting <- apply genBool g interrupting
    Just [text|
      attachedTo   = $ncontainer
      interrupting = $ninterrupting|]

genTimeDefinition :: BpmnGraph -> Node -> Maybe Text
genTimeDefinition = isTimed =>> f
  where f g n = timeInformation g !? n >>= genTimeInformation n

genTimeReference :: BpmnGraph -> Node -> Maybe Text
genTimeReference = isTimed =>> f
  where f _ n = let tmode = toText n <> "time" in Just [text|mode = $tmode|]

-- evolutions:
-- - add timezones
-- - take into account a parametric time start (not 1970-01-01T00:00:00)
--    note: this will require supporting negative numbers
-- - signal errors at parsing or transforming
--
genTimeInformation :: Node -> TimerEventDefinition -> Maybe Text
genTimeInformation n (TimerEventDefinition (Just tdt) (Just tdv)) =
  genTimeInformation' tdt (toText tdv) (toText n)
genTimeInformation _ (TimerEventDefinition _ _) = Nothing

genTimeInformation' :: TimerDefinitionType -> Text -> Text -> Maybe Text
genTimeInformation' TimeDate val n = do
  let parsed = parse parseDateTime val
  res <- maybeResult parsed
  let vval = dateToAlloy res
  let ni   = n <> "time"
  Just [text|one sig $ni extends Date {} {
    date = $vval
  }|]
genTimeInformation' TimeDuration val n = do
  let parsed = parse parseDuration val
  res <- maybeResult parsed
  let vval = durationToAlloy res
  let ni   = n <> "time"
  Just [text|one sig $ni extends Duration {} {
    duration = $vval
  }|]
genTimeInformation' TimeCycle val n = do
  let parsed =
        [flip parse val]
          <*> [parseCycleStart, parseCycleEnd, parseCycleDuration]
  ti@(dtype, _, _, _) <- msum $ maybeResult <$> parsed
  ncontents           <- genTimeInformation'' ti
  let ntype = show dtype
  let ni    = n <> "time"
  Just [text|one sig $ni extends $ntype {} {
    $ncontents
  }|]

genTimeInformation'' :: ( TimeCycleSubtype
                        , Maybe Integer
                        , CalendarDiffTime
                        , Maybe UTCTime
                        )
                     -> Maybe Text
genTimeInformation'' (CycleStart, nb, dur, dat) = do
  nbase <- genTimeInformation'' (CycleDuration, nb, dur, dat)
  ndat  <- dateToAlloy <$> dat
  Just [text|$nbase
    startdate = $ndat|]
genTimeInformation'' (CycleEnd, nb, dur, dat) = do
  nbase <- genTimeInformation'' (CycleDuration, nb, dur, dat)
  ndat  <- dateToAlloy <$> dat
  Just [text|$nbase
    enddate = $ndat|]
genTimeInformation'' (CycleDuration, nb, dur, _) = do
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
