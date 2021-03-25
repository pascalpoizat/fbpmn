module Fbpmn.BpmnGraph.IO.Bpmn where

import qualified Data.ByteString.Lazy as BS
  ( readFile,
  )
import qualified Data.Map as M
  ( empty,
    fromList,
    singleton,
  )
import Fbpmn.BpmnGraph.Model
import Fbpmn.BpmnGraph.SpaceModel
import Fbpmn.Helper (Id, Parser, TEither, eitherResult, parse, parseContainer, parseCouple, parseIdentifier, parseList, tlift2, withPrefixedIndex, (?#), parseTerminal, FReader (FR))
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )
import Text.XML.Light
  ( Content (..),
    Element (..),
    QName (..),
    cdData,
    elChildren,
    filterChildren,
    findAttr,
    findChild,
    findChildren,
    onlyElems,
    parseXML,
    ppElement,
  )

--
-- helpers for building QNames
--

-- BPMN

uri :: String
uri = "http://www.omg.org/spec/BPMN/20100524/MODEL"

prefix :: String
prefix = "bpmn"

nA :: String -> QName
nA s = QName s Nothing Nothing

nE :: String -> QName
nE s = QName s (Just uri) (Just prefix)

-- Camunda

camundaUri :: String
camundaUri = "http://camunda.org/schema/1.0/bpmn"

camundaPrefix :: String
camundaPrefix = "camunda"

nCA :: String -> QName
nCA s = QName s Nothing Nothing

nCE :: String -> QName
nCE s = QName s (Just camundaUri) (Just camundaPrefix)

-- Space BPMN

spaceUri :: String
spaceUri = "" -- none

spacePrefix :: String
spacePrefix = "fbpmn-space"

nSA :: String -> QName
nSA s = QName s Nothing Nothing

nSE :: String -> QName
nSE s = QName s Nothing (Just spacePrefix)

--
-- helpers to get attributes
--

aOrElseB :: String -> String -> Element -> Maybe String
aOrElseB an1 an2 e = do
  let av1 = findAttr (nA an1) e
  let av2 = findAttr (nA an2) e
  fromMaybe av2 (Just av1)

aOrElseB' :: String -> String -> String -> Element -> String
aOrElseB' def an1 an2 e = do
  let av1 = findAttr (nA an1) e
  let av2 = findAttr (nA an2) e
  fromMaybe (fromMaybe def av2) av1

--
-- helpers for predicates
--

(?=) :: String -> Element -> Bool
(?=) s = (==) (nE s) . elName

oneOf :: Element -> [Element -> Bool] -> Bool
oneOf e ps = getAny . foldMap Any $ ps <*> [e]

oneMaybeOf :: Element -> [Element -> Maybe a] -> Bool
oneMaybeOf e ps = any isJust $ ps <*> [e]

--
-- helpers for ids
--

getId :: Element -> Maybe String
getId = findAttr (nA "id")

getName :: Element -> Maybe String
getName = findAttr (nA "name")

isIdOf :: String -> Element -> Maybe Bool
isIdOf s e = do
  ie <- getId e
  pure (ie == s)

isNameOf :: String -> Element -> Maybe Bool
isNameOf s e = do
  ne <- getName e
  pure (ne == s)

isIdOf' :: String -> Element -> Bool
isIdOf' s e = fromMaybe False $ isIdOf s e

isNameOf' :: String -> Element -> Bool
isNameOf' s e = fromMaybe False $ isNameOf s e

findById :: [Element] -> String -> Maybe Element
findById es eid = do
  ess <- nonEmpty [e | e <- es, isIdOf' eid e]
  Just $ head ess

findByName :: [Element] -> String -> Maybe Element
findByName es ename = do
  ess <- nonEmpty [e | e <- es, isNameOf' ename e]
  Just $ head ess

findByIds :: [Element] -> [String] -> [Element]
findByIds es ids = [e | e <- es, eid <- ids, isIdOf' eid e]

--
-- helpers for names vs ids
--

nameOrElseId :: Element -> Maybe String
nameOrElseId = aOrElseB "name" "id"

hasChildren :: QName -> Element -> Bool
hasChildren q = not . null . findChildren q

-- message events
pMx :: Element -> Bool
pMx = hasChildren (nE "messageEventDefinition")

pTx :: Element -> Bool
pTx = hasChildren (nE "terminateEventDefinition")

pCx :: Element -> Bool
pCx = hasChildren (nE "conditionExpression")

pIx :: Element -> Bool
pIx e = case findAttr (nA "cancelActivity") e of
  Just "false" -> False
  Just _ -> True -- cancelActivity by default
  Nothing -> True -- cancelActivity by default
  -- timer events

pTimex :: Element -> Bool
pTimex = hasChildren (nE "timerEventDefinition")

pTimerDefinitionType' :: Element -> Maybe TimerDefinitionType
pTimerDefinitionType' e = case () of
  _
    | hasChildren (nE "timeDate") e -> Just TimeDate
    | hasChildren (nE "timeDuration") e -> Just TimeDuration
    | hasChildren (nE "timeCycle") e -> Just TimeCycle
    | otherwise -> Nothing

pTimerDefinitionValue' :: Element -> Maybe TimerValue
pTimerDefinitionValue' e = do
  contents <- elContent <$> eval
  content1 <- listToMaybe contents
  case content1 of
    Text cdata -> Just $ cdData cdata
    Elem _ -> Nothing
    CRef _ -> Nothing
  where
    eval = case () of
      _
        | hasChildren (nE "timeDate") e -> findChild (nE "timeDate") e
        | hasChildren (nE "timeDuration") e -> findChild (nE "timeDuration") e
        | hasChildren (nE "timeCycle") e -> findChild (nE "timeCycle") e
        | otherwise -> Nothing

pTimerDefinitionType :: Element -> Maybe TimerDefinitionType
pTimerDefinitionType e =
  pTimerDefinitionType' =<< findChild (nE "timerEventDefinition") e

pTimerDefinitionValue :: Element -> Maybe TimerValue
pTimerDefinitionValue e =
  pTimerDefinitionValue' =<< findChild (nE "timerEventDefinition") e

-- start events
-- NSE, MSE, or TSE
-- other start events are assimilated to NSE
pSE :: [Element] -> Element -> Bool
pSE _ = (?=) "startEvent"

pMSE :: [Element] -> Element -> Maybe NodeType
pMSE es e = if pSE es e && pMx e then Just MessageStartEvent else Nothing

pTSE :: [Element] -> Element -> Maybe NodeType
pTSE es e =
  if pSE es e && pTimex e then Just TimerStartEvent else Nothing

pNSE :: [Element] -> Element -> Maybe NodeType
pNSE es e =
  if pSE es e && not (e `oneMaybeOf` [pMSE es, pTSE es])
    then Just NoneStartEvent
    else Nothing

-- intermediary events
-- CMIE, TMIE, or (C)TIE
-- other intermediary events are discarded
pITE :: [Element] -> Element -> Bool
pITE _ = (?=) "intermediateThrowEvent"

pTMIE :: [Element] -> Element -> Maybe NodeType
pTMIE es e =
  if pITE es e && pMx e then Just ThrowMessageIntermediateEvent else Nothing

pICE :: [Element] -> Element -> Bool
pICE _ = (?=) "intermediateCatchEvent"

pCMIE :: [Element] -> Element -> Maybe NodeType
pCMIE es e =
  if pICE es e && pMx e then Just CatchMessageIntermediateEvent else Nothing

pCTIE :: [Element] -> Element -> Maybe NodeType
pCTIE es e =
  if pICE es e && pTimex e
    then Just TimerIntermediateEvent
    else Nothing

pIE :: [Element] -> Element -> Bool
pIE es e = e `oneMaybeOf` [pTMIE es, pCMIE es, pCTIE es]

-- end events
-- NEE, MEE, or TEE
-- other end events are assimilated to NEE
pEE :: [Element] -> Element -> Bool
pEE _ = (?=) "endEvent"

pMEE :: [Element] -> Element -> Maybe NodeType
pMEE es e = if pEE es e && pMx e then Just MessageEndEvent else Nothing

pTEE :: [Element] -> Element -> Maybe NodeType
pTEE es e = if pEE es e && pTx e then Just TerminateEndEvent else Nothing

pNEE :: [Element] -> Element -> Maybe NodeType
pNEE es e =
  if pEE es e && not (e `oneMaybeOf` [pMEE es, pTEE es])
    then Just NoneEndEvent
    else Nothing

-- boundary events
-- MBE or TBE (default is interrupting, i.e., cancelActivity=true if not given)
-- other boundary events are discarded
pBE :: [Element] -> Element -> Bool
pBE _ = (?=) "boundaryEvent"

pMBE :: [Element] -> Element -> Maybe NodeType
pMBE es e = if pBE es e && pMx e then Just MessageBoundaryEvent else Nothing

pTBE :: [Element] -> Element -> Maybe NodeType
pTBE es e = if pBE es e && pTimex e then Just TimerBoundaryEvent else Nothing

pCancelActivity :: Element -> Bool
pCancelActivity e = case findAttr (nA "cancelActivity") e of
  Just "false" -> False
  Just _ -> True -- boundary events are interrupting by default
  Nothing -> True -- boundary events are interrupting by default

-- time-related events
pTE :: [Element] -> Element -> Bool
pTE es e = e `oneMaybeOf` [pTSE es, pCTIE es, pTBE es]

-- events
pE :: [Element] -> Element -> Bool
pE es e = e `oneOf` [pSE es, pIE es, pEE es, pBE es]

-- gateways
pAndGateway :: [Element] -> Element -> Maybe NodeType
pAndGateway _ e = if (?=) "parallelGateway" e then Just AndGateway else Nothing

pOrGateway :: [Element] -> Element -> Maybe NodeType
pOrGateway _ e = if (?=) "inclusiveGateway" e then Just OrGateway else Nothing

pEventBasedGateway :: [Element] -> Element -> Maybe NodeType
pEventBasedGateway _ e =
  if (?=) "eventBasedGateway" e then Just EventBasedGateway else Nothing

pXorGateway :: [Element] -> Element -> Maybe NodeType
pXorGateway _ e =
  if (?=) "exclusiveGateway" e then Just XorGateway else Nothing

pGateway :: [Element] -> Element -> Bool
pGateway es e =
  e
    `oneMaybeOf` [ pAndGateway es,
                   pOrGateway es,
                   pXorGateway es,
                   pEventBasedGateway es
                 ]

-- tasks
-- AT, ST, or RT
-- {user,service,script,manual,business rule} tasks are treated as AT
pST :: [Element] -> Element -> Maybe NodeType
pST _ e = if (?=) "sendTask" e then Just SendTask else Nothing

pRT :: [Element] -> Element -> Maybe NodeType
pRT _ e = if (?=) "receiveTask" e then Just ReceiveTask else Nothing

pAT :: [Element] -> Element -> Bool
pAT _ = (?=) "task"

pUT :: [Element] -> Element -> Bool
pUT _ = (?=) "userTask"

pXT :: [Element] -> Element -> Bool
pXT _ = (?=) "scriptTask"

pWT :: [Element] -> Element -> Bool
pWT _ = (?=) "serviceTask"

pMT :: [Element] -> Element -> Bool
pMT _ = (?=) "manualTask"

pBT :: [Element] -> Element -> Bool
pBT _ = (?=) "businessRuleTask"

pAsAT :: [Element] -> Element -> Maybe NodeType
pAsAT es e =
  if e `oneOf` ([pAT, pUT, pWT, pXT, pBT, pMT] <*> [es])
    then Just AbstractTask
    else Nothing

pT :: [Element] -> Element -> Bool
pT es e = e `oneMaybeOf` [pAsAT es, pST es, pRT es]

-- activities
pSPx :: [Element] -> Element -> Bool
pSPx _ = (?=) "subProcess"

pSP :: [Element] -> Element -> Maybe NodeType
pSP es e = if pSPx es e then Just SubProcess else Nothing

pA :: [Element] -> Element -> Bool
pA es e = e `oneOf` ([pT, pSPx] <*> [es])

-- processes
pP :: [Element] -> Element -> Bool
pP _ = (?=) "process"

-- nodes
pNode :: [Element] -> Element -> Bool
pNode es e = e `oneOf` ([pE, pGateway, pA, pP] <*> [es])

-- edges
-- sequence flows are NSF, CSF or DSF
pMF :: [Element] -> Element -> Bool
pMF _ = (?=) "messageFlow"

pSF :: [Element] -> Element -> Bool
pSF _ = (?=) "sequenceFlow"

pCSF :: [Element] -> Element -> Bool
pCSF es e = pSF es e && pCx e

-- for e to be a DSF it is a bit more complicated
-- 1. type of e is sequenceFlow
-- 2. e.sourceRef.default = e.id
pDSF :: [Element] -> Element -> Bool
pDSF es e = fromMaybe False $ do
  sa <- findAttr (nA "sourceRef") e
  sn <- findById es sa
  def <- findAttr (nA "default") sn
  pure $ pSF es e && isIdOf' def e

pNSF :: [Element] -> Element -> Bool
pNSF es e = pSF es e && not (e `oneOf` [pCSF es, pDSF es])

pEdge :: [Element] -> Element -> Bool
pEdge es e = e `oneOf` [pSF es, pMF es]

dump :: [Element] -> Text
dump es = unlines $ toText . ppElement <$> es

xDecode :: String -> Parser a -> [Element] -> TEither a
xDecode s parser elements = do
  element <- findByName elements s ?# toText ("missing " <> s)
  value <- findAttr (nA "value") element ?# toText ("missing value for " <> s)
  first toText $ eitherResult $ parse parser (toText value)

-- |
-- An experimental Space BPMN reading.
decodeS :: [Content] -> TEither SpaceBpmnGraph
decodeS cs = do
  -- base graph can be decoded directly
  g <- decode cs
  -- top-level elements
  let topElements = onlyElems cs
  -- conditional edges
  let eCs = edgesT g ConditionalSequenceFlow
  -- collaboration extension (for 1st collaboration to be found)
  c <- listToMaybe (concatMap (findChildren (nE "collaboration")) topElements) ?# "missing collaboration"
  cEx <- findChild (nE "extensionElements") c ?# "missing collaboration-level extension elements"
  cCPs <- findChild (nCE "properties") cEx ?# "missing camunda:properties in bpmn:extensionElements"
  let cExAll = elChildren cCPs
  -- collaboration->extensionElements->*->true/name=base-locations.value
  bs <- xDecode "base-locations" parseIdList cExAll
  -- collaboration->extensionElements->*->true/name=group-locations.value
  gs <- xDecode "group-locations" parseIdList cExAll
  -- collaboration->extensionElements->*->true/name=transitions.value
  ts <- xDecode "transitions" parseTransition cExAll
  let its = withPrefixedIndex "se_" ts
  let es = toString . fst <$> its
  let sEs = fromList $ bimap toString fst <$> its
  let tEs = fromList $ bimap toString snd <$> its
  -- collaboration->extensionElements->*->true/name=initial-space.value
  initSpRaw <- xDecode "initial-space" parseIdToIdListList cExAll
  let initSp = M.fromList initSpRaw
  -- 
  cvs <- pure M.empty -- TODO:
  cks <- pure M.empty -- TODO:
  cfs <- pure M.empty -- TODO:
  co <- pure M.empty -- TODO:
  as <- pure M.empty -- TODO:
  initLs <- pure M.empty -- TODO:
  vs <- pure [] -- TODO:
  -- space structure
  let s = SpaceStructure bs gs es sEs tEs
  -- initial configuration
  let i = SpaceConfiguration initLs initSp
  pure $
    SpaceBPMNGraph
      g
      s
      vs
      cvs
      cks
      cfs
      co
      as
      i

-- | Parse a list [(Id, [Id])] that can be used too generate a map with fromList.
-- Format is {id1: [id11, ...], ...} where ids are identifiers
parseIdToIdListList :: Parser [(Id, [Id])]
parseIdToIdListList = parseContainer "{" "}" "," parseIdIdListCouple

-- |  Parse a transition.
--  Format is [(s,t)i, ...] where si an ti are identifiers.
parseTransition :: Parser [(Id, Id)]
parseTransition = parseContainer "[" "]" "," parseIdCouple

-- | Parse a couple of Ids.
-- Format is (id1, id2) where id1 and id2 are Ids.
parseIdCouple :: Parser (Id, Id)
parseIdCouple = parseCouple parseIdentifier parseIdentifier

-- | Parse a list [Id]
-- Format is [id1, id2, ...] where ids are identifiers.
parseIdList :: Parser [Id]
parseIdList = parseList parseIdentifier

-- | Parse a couple (Id, [Id]).
-- Format is (id1 : [id11, ...], ...)
parseIdIdListCouple :: Parser (Id, [Id])
parseIdIdListCouple = do
  k <- parseIdentifier
  _ <- parseTerminal ":"
  v <- parseIdList
  return (k, v)

-- |
-- An experimental BPMN reading.
--
-- Requirements:
-- - collaboration has a name
-- - message flows have a name (used as message type)
--
-- Enhancements:
-- - remove duplicates in cMessageTypes
decode :: [Content] -> TEither BpmnGraph
decode cs = do
  -- top-level elements
  let topElements = onlyElems cs
  -- collaboration (1st one to be found)
  c <- listToMaybe (concatMap (findChildren (nE "collaboration")) topElements) ?# "missing collaboration"
  cId <- getId c ?# "missing collaboration id"
  -- participants
  let cParticipants = findChildren (nE "participant") c
  cParticipantRefs <- sequence (findAttr (nA "processRef") <$> cParticipants) ?# "missing process reference"
  -- cParticipantIds <- sequence $ getId <$> cParticipants
  -- processes
  let allProcesses = concatMap (findChildren (nE "process")) topElements
  let cProcesses = findByIds allProcesses cParticipantRefs
  -- message flows and messages
  let cMessageFlows = findChildren (nE "messageFlow") c
  cMessageFlowIds <- sequence (getId <$> cMessageFlows) ?# "missing id in a message flow"
  cMessageTypes <- (sequence . hashNub $ nameOrElseId <$> cMessageFlows) ?# "missing type in a message flow"
  -- high level information (collaboration level)
  let g =
        BpmnGraph
          (toText cId)
          cParticipantRefs
          cMessageFlowIds
          (M.fromList $ ccatN <$> cParticipantRefs)
          (M.fromList $ ccatE <$> cMessageFlowIds)
          (M.fromList $ catMaybes $ tlift2 . bsource <$> cMessageFlows)
          (M.fromList $ catMaybes $ tlift2 . btarget <$> cMessageFlows)
          M.empty -- (M.fromList $ catMaybes $ tlift2 . bname <$> cParticipants)
          M.empty
          M.empty
          M.empty
          cMessageTypes
          (M.fromList $ catMaybes $ tlift2 . bname <$> cMessageFlows)
          M.empty
          M.empty
  -- compute for participant processes
  processGraphs <- sequence $ compute <$> cProcesses
  pure $ g <> mconcat processGraphs
  where
    ccatE :: String -> (Edge, EdgeType)
    ccatE e = (e, MessageFlow)
    ccatN :: String -> (Node, NodeType)
    ccatN e = (e, Process)

-- | Computes a map from a predicate and transformation.
-- - p is a predicate that is used to select only some elements from a context
-- - f is a transformation of an element into a couple element id x element information
computeMap :: Ord k => ([Element] -> Element -> Bool) -> (Element -> (Maybe k, Maybe a)) -> Element -> Map k a
computeMap p f e = M.fromList $ catMaybes $ tlift2 . f <$> ks
  where
    aes = elChildren e
    ks = filterChildren (p aes) e

compute :: Element -> TEither BpmnGraph
compute e = do
  let allElements = elChildren e
  pid <- getId e ?# "missing process identifier"
  let ns = filterChildren (pNode allElements) e
  nids <- sequence (getId <$> ns) ?# "missing node identifier"
  let es = filterChildren (pEdge allElements) e
  eids <- sequence (getId <$> es) ?# "missing edge identifier"
  let sps = findChildren (nE "subProcess") e
  let g =
        BpmnGraph
          ""
          nids -- node ids
          eids -- edge ids
          (computeMap pNode (bcatN allElements) e) -- (n, catN(n)) for n in N
          (computeMap pEdge (bcatE allElements) e) -- (e, catE(n)) for e in E
          (computeMap pEdge bsource e) -- (e, sourceE(e)) for e in E
          (computeMap pEdge btarget e) -- (e, targetE(e)) for e in E
          (computeMap pNode bname e) -- (n, nameN(n)) for n in N
          (M.singleton pid nids) -- (pid, containN(pid))
          (M.singleton pid eids) --- (pid, containE(pid))
          (computeMap pBE battached e) -- (n, attached(n)) for n in NBE
          [] -- no message inside a (sub-)process
          M.empty -- no message flows inside a (sub-)process
          (computeMap pBE bisInterrupting e) -- (n, isInterrupt(n)) for n in NBE
          (computeMap pTE btimeDefinition e) -- (n, timeInformation(n)) for n in NTE
  spgs <- sequence $ compute <$> sps
  pure $ g <> mconcat spgs

btimeDefinition :: Element -> (Maybe Node, Maybe TimerEventDefinition)
btimeDefinition n = (getId n, Just $ TimerEventDefinition ttype tval)
  where
    ttype = pTimerDefinitionType n
    tval = pTimerDefinitionValue n

bisInterrupting :: Element -> (Maybe Node, Maybe Bool)
bisInterrupting n = (getId n, Just $ pCancelActivity n)

battached :: Element -> (Maybe Node, Maybe Node)
battached n = (getId n, findAttr (nA "attachedToRef") n)

bsource :: Element -> (Maybe Edge, Maybe Node)
bsource mf = (getId mf, findAttr (nA "sourceRef") mf)

btarget :: Element -> (Maybe Edge, Maybe Node)
btarget mf = (getId mf, findAttr (nA "targetRef") mf)

bname :: Element -> (Maybe Edge, Maybe String)
bname mf = (getId mf, getName mf)

bcatN :: [Element] -> Element -> (Maybe Node, Maybe NodeType)
bcatN xs e = f e preds
  where
    preds =
      [ pNSE,
        pMSE,
        pTSE,
        pCMIE,
        pTMIE,
        pCTIE,
        pMBE,
        pTBE,
        pNEE,
        pMEE,
        pTEE,
        pAndGateway,
        pXorGateway,
        pOrGateway,
        pEventBasedGateway,
        pST,
        pRT,
        pAsAT,
        pSP
      ]
        <*> [xs]
    f :: Element -> [Element -> Maybe NodeType] -> (Maybe Node, Maybe NodeType)
    f e' [] = (getId e', Nothing)
    f e' (p : r) = if isJust res then (getId e', res) else f e' r
      where
        res = p e'

bcatE :: [Element] -> Element -> (Maybe Edge, Maybe EdgeType)
bcatE xs e = f e preds
  where
    f :: Element -> [(Element -> Bool, EdgeType)] -> (Maybe Edge, Maybe EdgeType)
    f e' ((p, t) : r) = if p e' then (getId e', Just t) else f e' r
    f e' [] = (getId e', Nothing)
    -- in preds, the order is important since a DSF validates pNSF
    preds =
      [ (pDSF xs, DefaultSequenceFlow),
        (pCSF xs, ConditionalSequenceFlow),
        (pNSF xs, NormalSequenceFlow),
        (pMF xs, MessageFlow)
      ]

-- | FReader from BPMN to BPMN Graph.
reader :: FReader BpmnGraph
reader = FR (readFromXML decode) ".bpmn"

-- | FReader from BPMN to Space BPMN Graph.
readerS :: FReader SpaceBpmnGraph
readerS = FR (readFromXML decodeS) ".bpmn"

-- | Read some model of type a from an XML file given an a decoder.
readFromXML :: ([Content] -> TEither a) -> FilePath -> IO (TEither a)
readFromXML d p = (d . parseXML <$> BS.readFile p) `catchIOError` handler
  where
    handler :: IOError -> IO (TEither a)
    handler e
      | isDoesNotExistError e = do
        putTextLn "file not found"
        pure $ Left "file not found"
      | otherwise = do
        putTextLn "unknown error"
        pure $ Left "unknown error"
