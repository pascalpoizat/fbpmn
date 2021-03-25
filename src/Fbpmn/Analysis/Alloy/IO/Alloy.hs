{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Alloy.IO.Alloy where

import           Fbpmn.BpmnGraph.Model
import           NeatInterpolation              ( text )
import           Data.Map.Strict                ( (!?) )
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
import Fbpmn.Helper (FWriter (FW))

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
-- [X] TBE interrupting + cycle duration
-- [X] TBE interrupting + infinite cycle duration
-- [X] TBE interrupting + cycle start/duration
-- [X] TBE interrupting + infinite cycle start/duration
-- [X] TBE interrupting + cycle duration/end
-- [X] TBE interrupting + infinite cycle duration/end
-- [X] TBE non interrupting + cycle duration
-- [X] TBE non interrupting + infinite cycle duration
-- [X] TBE non interrupting + cycle start/duration
-- [X] TBE non interrupting + infinite cycle start/duration
-- [X] TBE non interrupting + cycle duration/end
-- [X] TBE non interrupting + infinite cycle duration/end
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
type TR c a = c -> a -> Maybe Text

-- transformer application (over a list of as)
applyN :: TR c a -> c -> [a] -> Maybe Text
applyN f c as = Just . unlines . catMaybes $ f c <$> as

-- constrain a transformer with a predicate
infixr 0 =>>
(=>>) :: Pred c a -> TR c a -> TR c a
p =>> t = \c a -> if p c a then t c a else Nothing

-- predicate wrt being of a type defined in the context
ofType :: (Eq a) => Selector c a t -> TypePred c a t
ofType s ts c a = a `elem` s c ts

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

type NodeTypePred = TypePred BpmnGraph Node NodeType
type EdgeTypePred = TypePred BpmnGraph Edge EdgeType
type NodePred = Pred BpmnGraph Node
type EdgePred = Pred BpmnGraph Edge

inNodeTypes :: NodeTypePred
inNodeTypes = ofType nodesTs

inEdgeTypes :: EdgeTypePred
inEdgeTypes = ofType edgesTs

isTimed :: NodePred
isTimed = inNodeTypes [nTSE, nTICE, nTBE]

isContainer :: NodePred
isContainer = inNodeTypes [nSP, nP]

isBoundaryEvent :: NodePred
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
genBool :: TR () Bool
genBool _ True  = Just "True"
genBool _ False = Just "False"

-- | FWriter from BPMN Graph to Alloy.
writer :: FWriter BpmnGraph
writer = FW writeToAlloy ".als"

{-|
Write a BPMN Graph to an Alloy file.
-}
writeToAlloy :: FilePath -> BpmnGraph -> IO ()
writeToAlloy p = writeFile p . toString . encodeBpmnGraphToAlloy

{-|
Transform a BPMN Graph to an Alloy specification.
-}
encodeBpmnGraphToAlloy :: BpmnGraph -> Text
encodeBpmnGraphToAlloy g =
  unlines
    .   catMaybes
    $   [genHeader, genMessages, genNodes, genEdges]
    <*> [()]
    <*> [g]

genHeader :: TR () BpmnGraph
genHeader _ g =
  let mname = name g
  in  Just [text|
      module $mname

      open PWSSyntax
      open PWSProp|]

genMessages :: TR () BpmnGraph
genMessages _ g = applyN genMessage g $ messages g

genNodes :: TR () BpmnGraph
genNodes _ g = applyN genNode g $ nodes g

genEdges :: TR () BpmnGraph
genEdges _ g = applyN genEdge g $ edges g

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

genMessage :: TR BpmnGraph Message
genMessage _ m = Just [text|one sig $mname extends Message {}|]
  where mname = toText m

genNode :: TR BpmnGraph Node
genNode g n = do
  ntype <- nodeTypeToAlloy <$> (catN g !? n)
  let tinfo = fromMaybe "" $ genTimeDefinition g n
  let nname = toText n
  let values =
        unlines
          .   catMaybes
          $   [genContainment, genBoundaryInformation, genTimeReference]
          <*> [g]
          <*> [n]
  Just [text|
  $tinfo
  one sig $nname extends $ntype {} {$values}
  |]

genEdge :: TR BpmnGraph Edge
genEdge g e = Just [text|one sig $ename extends $etype {} {$values}|]
 where
  ename = toText e
  etype = maybe "" edgeTypeToAlloy (catE g !? e)
  values =
    unlines . catMaybes $ [genFlow, genMessageInformation] <*> [g] <*> [e]

genContainment :: TR BpmnGraph Node
genContainment = isContainer =>> f
 where
  f g n =
    let nces = toText $ intercalate " + " $ concat (containN g !? n)
    in  Just [text|contains = $nces|]

genBoundaryInformation :: TR BpmnGraph Node
genBoundaryInformation = isBoundaryEvent =>> f
 where
  f g n = do
    ncontainer    <- toText <$> attached g !? n
    interrupting  <- Just $ fromMaybe True $ isInterrupt g !? n
    ninterrupting <- genBool () interrupting
    Just [text|
      attachedTo   = $ncontainer
      interrupting = $ninterrupting|]

genTimeDefinition :: TR BpmnGraph Node
genTimeDefinition = isTimed =>> f
  where f g n = timeInformation g !? n >>= genTimeInformation n

genTimeReference :: TR BpmnGraph Node
genTimeReference = isTimed =>> f
  where f _ n = let tmode = toText n <> "time" in Just [text|mode = $tmode|]

-- evolutions:
-- - add timezones
-- - take into account a parametric time start (not 1970-01-01T00:00:00)
--    note: this will require supporting negative numbers
-- - signal errors at parsing or transforming
--
genTimeInformation :: TR Node TimerEventDefinition
genTimeInformation n ted = do
  tdt <- timerDefinitionType ted
  tdv <- timerDefinitionValue ted
  genTimeInformation' (tdt, n) tdv

genTimeInformation' :: TR (TimerDefinitionType, Node) TimerValue
genTimeInformation' (TimeDate, n) val = do
  let parsed = parse parseDateTime $ toText val
  res  <- maybeResult parsed
  vval <- genDate () res
  let ni = toText n <> "time"
  Just [text|one sig $ni extends Date {} {
    date = $vval
  }|]
genTimeInformation' (TimeDuration, n) val = do
  let parsed = parse parseDuration $ toText val
  res  <- maybeResult parsed
  vval <- genDuration () res
  let ni = toText n <> "time"
  Just [text|one sig $ni extends Duration {} {
    duration = $vval
  }|]
genTimeInformation' (TimeCycle, n) val = do
  let parsed =
        [flip parse $ toText val]
          <*> [parseCycleStart, parseCycleEnd, parseCycleDuration]
  (dtype, dnb, dduration, ddate) <- msum $ maybeResult <$> parsed
  ncontents <- genTimeInformation'' dtype (dnb, dduration, ddate)
  let ntype = show dtype
  let ni    = toText n <> "time"
  Just [text|one sig $ni extends $ntype {} {
    $ncontents
  }|]

genTimeInformation'' :: TR
                          TimeCycleSubtype
                          (Maybe Integer, CalendarDiffTime, Maybe UTCTime)
genTimeInformation'' CycleStart (nb, dur, dat) = do
  nbase <- genTimeInformation'' CycleDuration (nb, dur, dat)
  ndat  <- genDate () =<< dat
  Just [text|$nbase
    startdate = $ndat|]
genTimeInformation'' CycleEnd (nb, dur, dat) = do
  nbase <- genTimeInformation'' CycleDuration (nb, dur, dat)
  ndat  <- genDate () =<< dat
  Just [text|$nbase
    enddate = $ndat|]
genTimeInformation'' CycleDuration (nb, dur, _) = do
  let nnb  = maybe genUndef show nb
  vval <- genDuration () dur
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
  n   <- option 0 parseInteger
  _   <- parseTerminal "/"
  dt  <- parseDateTime
  _   <- parseTerminal "/"
  dur <- parseDuration
  return (CycleStart, if n==0 then Nothing else Just n, dur, Just dt)

-- R(n)/Duration/DateTime
parseCycleEnd :: Parser
                   ( TimeCycleSubtype
                   , Maybe Integer
                   , CalendarDiffTime
                   , Maybe UTCTime
                   )
parseCycleEnd = do
  _   <- parseTerminal "R"
  n   <- option 0 parseInteger
  _   <- parseTerminal "/"
  dur <- parseDuration
  _   <- parseTerminal "/"
  dt  <- parseDateTime
  return (CycleEnd, if n==0 then Nothing else Just n, dur, Just dt)

-- R(n)/Duration
parseCycleDuration :: Parser
                        ( TimeCycleSubtype
                        , Maybe Integer
                        , CalendarDiffTime
                        , Maybe UTCTime
                        )
parseCycleDuration = do
  _ <- parseTerminal "R"
  n <- option 0 parseInteger
  _ <- parseTerminal "/"
  c <- parseDuration
  return (CycleDuration, if n==0 then Nothing else Just n, c, Nothing)

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

genFlow :: TR BpmnGraph Edge
genFlow g e = do
  sn1 <- toText <$> sourceE g !? e
  sn2 <- toText <$> targetE g !? e
  Just [text|
      source = $sn1
      target = $sn2
    |]

genMessageInformation :: TR BpmnGraph Edge
genMessageInformation g e = do
  m <- toText <$> messageE g !? e
  Just [text|message = $m|]

genDate :: TR () UTCTime
genDate _ = Just . timeToAlloy utcTimeToPOSIXSeconds

genDuration :: TR () CalendarDiffTime
genDuration _ = Just . timeToAlloy ctTime

timeToAlloy :: (a -> NominalDiffTime) -> a -> Text
timeToAlloy f = show . truncate . nominalDiffTimeToSeconds . f
