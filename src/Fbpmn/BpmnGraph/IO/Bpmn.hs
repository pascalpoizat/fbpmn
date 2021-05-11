{-# LANGUAGE QuasiQuotes #-}

module Fbpmn.BpmnGraph.IO.Bpmn where

import qualified Data.ByteString.Lazy as BS
  ( readFile,
  )
import qualified Data.Map as M
  ( empty,
    fromList,
    singleton, map, elems
  )
import Fbpmn.BpmnGraph.Model
import Fbpmn.BpmnGraph.SpaceModel
import Fbpmn.Helper (Id, Parser, TEither, parse, parseContainer, parseCouple, parseIdentifier, parseList, withPrefixedIndex, (?#), parseTerminal, FReader (FR), eitherResult, ith1, ith2, ith3)
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )
import Text.XML.Light
  ( Content (..),
    Element (..),
    QName (..),
    CData (..),
    cdData,
    elChildren,
    filterChildren,
    findAttr,
    findChild,
    findChildren,
    onlyElems,
    parseXML,
    ppElement
  )
import Relude.Extra.Lens ((.~))

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

pXor :: [Element] -> Element -> Bool
pXor _ = (?=) "exclusiveGateway"

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

-- | Parse a string given a parser.
-- Whitespace is added to the string to deal with a bug with identifier parsing.
xParseWith :: Parser a -> String -> TEither a
xParseWith p s = first toText $ eitherResult $ parse p (toText $ s ++ " ")

xFindElement :: (String -> QName) -> String -> Element -> TEither Element
xFindElement f s parentElement = findChild (f s) parentElement ?# toText ("missing element " <> s <> " in " <> show parentElement)

xFindName :: String -> Element -> TEither Element
xFindName s parentElement = findByName (elChildren parentElement) s ?# toText ("missing element with name " <> s <> " in " <> show parentElement)

xFindAttribute :: (String -> QName) -> String -> Element -> TEither String
xFindAttribute f s element = findAttr (f s) element ?# toText ("missing attribute " <> s <> " in " <> show element)

xFindElement' :: (String -> QName) -> String -> [Element] -> TEither Element
xFindElement' f s parentElements = listToMaybe (concatMap (findChildren (f s)) parentElements) ?# toText ("missing element " <> s <> " in " <> show parentElements)

xFindElements :: (String -> QName) -> String -> Element -> TEither [Element]
xFindElements f s parentElement = Right $ findChildren (f s) parentElement

xFindElements' :: (String -> QName) -> String -> [Element] -> TEither [Element]
xFindElements' f s parentElements = Right $ concatMap (findChildren (f s)) parentElements

xFindContent :: Element -> TEither Id
xFindContent e = case elContent e of
  [CRef s] -> Right s
  [Text (CData _ s _)] -> Right s
  _ -> Left $ "needed single CRef at " <> show e

--
-- basic (/: for element, /. for attribute, /? foor name)
--

(/:) :: TEither Element -> String -> TEither Element
(/:) e s = e >>= xFindElement nE s

(/!) :: TEither Element -> String -> TEither Element
(/!) e s = e >>= xFindName s

(/.) :: TEither Element -> String -> TEither String
(/.) e s = e >>= xFindAttribute nA s

--
-- extension
--

(/::) :: TEither Element -> String -> TEither Element
(/::) e s = e >>= xFindElement nCE s

(/..) :: TEither Element -> String -> TEither String
(/..) e s = e >>= xFindAttribute nCA s

--
-- working on a list of elements (* prefix)
--

(*/:) :: TEither [Element] -> String -> TEither Element
(*/:) es s = es >>= xFindElement' nE s

--
-- requiring a list of children (no error if empty)
--

(/:*) :: TEither Element -> String -> TEither [Element]
(/:*) e s = e >>= xFindElements nE s

(/::*) :: TEither Element -> String -> TEither [Element]
(/::*) e s = e >>= xFindElements nCE s

(*/:*) :: TEither [Element] -> String -> TEither [Element]
(*/:*) es s = es >>= xFindElements' nE s

--
-- starting (< prefix)
--

(</:) :: Element -> String -> TEither Element
(</:) e s = pure e /: s

(</!) :: Element -> String -> TEither Element
(</!) e s = pure e /! s

(</.) :: Element -> String -> TEither String
(</.) e s = pure e /. s

(*</:) :: [Element] -> String -> TEither Element
(*</:) es s = pure es */: s

(</:*) :: Element -> String -> TEither [Element]
(</:*) e s = pure e /:* s

(*</:*) :: [Element] -> String -> TEither [Element]
(*</:*) es s = pure es */:* s

--
-- parsing and transformers
--

(@@) :: TEither String -> Parser a -> TEither a
(@@) s p = s >>= xParseWith p

asMap :: [(Id, a)] -> Map Id a
asMap = M.fromList

-- | An experimental Space BPMN reading.
decodeS :: [Content] -> TEither SpaceBpmnGraph
decodeS cs = do
  -- top-level elements
  let topElements = onlyElems cs
  -- base graph can be decoded directly
  graph <- decode cs
  -- collaboration extension (for 1st collaboration to be found)
  collaboration <- topElements *</: "collaboration"
  extension <- collaboration </: "extensionElements" /:: "properties"
  -- space structure
  bs <- extension </! "base-locations" /. "value" @@ parseIdList
  gs <- extension </! "group-locations" /. "value" @@ parseIdList
  ts <- extension </! "transitions" /. "value" @@ parseTransition
  let its = withPrefixedIndex "se_" ts
  let es = toString . fst <$> its
  let sEs = fromList $ bimap toString fst <$> its
  let tEs = fromList $ bimap toString snd <$> its
  let ss = SpaceStructure bs gs es sEs tEs
  -- initial space value
  isv <- extension </! "initial-space" /. "value" @@ parseIdToIdListList
  -- high level information (collaboration level)
  let collaborationSGraph =
        SpaceBpmnGraph
          graph
          ss
          []
          M.empty
          M.empty
          M.empty
          M.empty
          M.empty
          (SpaceConfiguration M.empty (M.fromList isv))
  -- compute for participant processes
  participants <- collaboration </:* "participant"
  processes <- topElements *</:* "process"
  participantReferences <- sequence (findAttr (nA "processRef") <$> participants) ?# "missing process reference"
  let cProcesses = findByIds processes participantReferences
  processSGraphs <- sequence $ computeS ss <$> cProcesses
  let sGraph = collaborationSGraph <> mconcat processSGraphs
  pure $ sGraph & variablesL .~ ordNub (computeUsedVariables sGraph)
  where
    computeUsedVariables sg =
      ["here", "_"]
      <> (M.elems . cVariables $ sg)
      <> mconcat (fVariables <$> (M.elems . cFormulas $ sg))
      <> (genLocName <$> ((`nodesT` Process) . graph $ sg))
    genLocName p = "loc" <> p

decodeCSFOrder :: Element -> TEither [Edge]
decodeCSFOrder e = do
  oes <- e </:* "outgoing"
  sequence $ xFindContent <$> oes

decodeA :: SpaceStructure -> Element -> TEither SpaceAction
decodeA ss e = do
  let extension = e </: "extensionElements" /:: "properties" /! "action"
  if isRight extension
    then extension /. "value" @@ parseSAction ss
    else pure SAPass

decodeF :: SpaceStructure -> Element -> TEither (Variable, FormulaKind, SpaceFormula)
decodeF ss e = do
  extension <- e </: "extensionElements" /:: "properties"
  fVariable <- extension </! "variable" /. "value"
  fKind <- extension </! "type" /. "value" @@ parseFKind
  fFormula <- extension </! "formula" /. "value" @@ parseSFormula ss
  pure (fVariable, fKind, fFormula)

parseSAction :: SpaceStructure -> Parser SpaceAction
parseSAction ss = parseSAMove ss <|> parseSAUpdate ss

parseSAMove :: SpaceStructure -> Parser SpaceAction
parseSAMove ss = do
  _ <- parseTerminal "move"
  _ <- parseTerminal "to"
  SAMove <$> parseSFormula ss

parseSAUpdate :: SpaceStructure -> Parser SpaceAction
parseSAUpdate _ = do
  _ <- parseTerminal "update"
  v <- parseIdentifier
  _ <- parseTerminal "from"
  l1 <- parseContainer "{" "}" "," parseIdentifier
  _ <- parseTerminal "to"
  l2 <- parseContainer "{" "}" "," parseIdentifier
  return $ SAUpdate v l1 l2

parseFKind :: Parser FormulaKind
parseFKind =
  (parseTerminal "all" >> return SFAll)
    <|> (parseTerminal "any" >> return SFAny)

-- | Parser for Space Formulas.
-- Requires the space structure to know if an identifier is a base location, a group location, or a variable.
-- A "." is required at the end of formulas.
parseSFormula :: SpaceStructure -> Parser SpaceFormula
parseSFormula s =
      (parseTerminal "true" >> return SFTrue)
  <|> (parseTerminal "here" >> return SFHere)
  <|> (parseTerminal "reachable" >> return SFReach )
  <|> do
        _ <- parseTerminal "reachable-from"
        SFReachFrom <$> parseIdentifier
  <|> do
        i <- parseIdentifier
        return $ (if i `elem` baseLocations s then SFBase else if i `elem` groupLocations s then SFGroup else SFVar) i
  <|> do
        _ <- parseTerminal "("
        _ <- parseTerminal "not"
        f <- parseSFormula s
        _ <- parseTerminal ")"
        return $ SFNot f
  <|> do
        _ <- parseTerminal "("
        f1 <- parseSFormula s
        _ <- parseTerminal "or"
        f2 <- parseSFormula s
        _ <- parseTerminal ")"
        return $ SFOr f1 f2
  <|> do
        _ <- parseTerminal "("
        f1 <- parseSFormula s
        _ <- parseTerminal "and"
        f2 <- parseSFormula s
        _ <- parseTerminal ")"
        return $ SFAnd f1 f2

computeS :: SpaceStructure -> Element -> TEither SpaceBpmnGraph
computeS ss e = do
  ces <- computeMap pCSF (bEdgeInfo $ decodeF ss ) e
  as <- computeMap pAT (bNodeInfo $ decodeA ss) e
  co <- computeMap pXor (bNodeInfo decodeCSFOrder) e
  -- initial location for processes only (not for sub processes)
  il <- if pP [] e
        then
          do
            pid <- e </. "id"
            loc <- e </: "extensionElements" /:: "properties" /! "initial-location" /. "value" @@ parseIdentifier
            pure $ M.singleton pid loc
        else pure M.empty
  let graph =
        SpaceBpmnGraph
          mempty -- the graph is read at the collaboration level
          mempty -- the space structure is read at the collaboration level
          [] -- the variables are computed at the end
          (M.map ith1 ces)
          (M.map ith2 ces)
          (M.map ith3 ces)
          co
          as
          (SpaceConfiguration il M.empty)
  subProcesses <- e </:* "subProcess"
  subProcessSGraphs <- sequence $ computeS ss <$> subProcesses
  pure $ graph <> mconcat subProcessSGraphs

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
  collaboration <- topElements *</: "collaboration"
  cId <- collaboration </. "id"
  -- participants
  participants <- collaboration </:* "participant"
  participantReferences <- sequence (findAttr (nA "processRef") <$> participants) ?# "missing process reference"
  -- message flows and messages
  cMessageFlows <- collaboration </:* "messageFlow"
  cMessageFlowIds <- sequence (getId <$> cMessageFlows) ?# "missing id in a message flow"
  cMessageTypes <- (sequence . hashNub $ nameOrElseId <$> cMessageFlows) ?# "missing type in a message flow"
  messageFlowSources <- computeMap pMF (bEdgeInfo bsource) collaboration
  messageFlowTargets <- computeMap pMF (bEdgeInfo btarget) collaboration
  messageFlowTypes <- computeMap pMF (bEdgeInfo bname) collaboration
  -- high level information (collaboration level)
  let collaborationGraph =
        BpmnGraph
          (toText cId)
          participantReferences
          cMessageFlowIds
          (M.fromList $ ccatN <$> participantReferences)
          (M.fromList $ ccatE <$> cMessageFlowIds)
          messageFlowSources
          messageFlowTargets
          M.empty
          M.empty
          M.empty
          M.empty
          cMessageTypes
          messageFlowTypes
          M.empty
          M.empty
  -- compute for participant processes
  processes <- topElements *</:* "process"
  let cProcesses = findByIds processes participantReferences
  processGraphs <- sequence $ compute <$> cProcesses
  pure $ collaborationGraph <> mconcat processGraphs
  where
    ccatE :: String -> (Edge, EdgeType)
    ccatE e = (e, MessageFlow)
    ccatN :: String -> (Node, NodeType)
    ccatN e = (e, Process)

-- | Computes a map from a predicate and transformation (signals errors).
-- - p is a predicate that is used to select only some elements from a context
-- - f is a transformation of an element into a couple element id x element information
computeMap :: Ord k => ([Element] -> Element -> Bool) -> (Element -> (TEither k, TEither a)) -> Element -> TEither (Map k a)
computeMap p f e =
    case ks of
      [] -> Right M.empty -- if no elements are selected by p then OK with empty map
      _  -> do -- else possibly KO
              mappedKeys <- sequence $ combine . f <$> ks
              pure $ M.fromList mappedKeys
  where
    ks = filterChildren (p $ elChildren e) e
    combine :: (TEither a, TEither b) -> TEither (a, b)
    combine (Left err1, Right _) = Left err1
    combine (Right _, Left err2) = Left err2
    combine (Left err1, Left err2) = Left $ err1 <> " / " <> err2
    combine (Right a, Right b) = Right (a, b)

-- | Computes a map from a predicate and transformation (does not signal errors, keeps only values that are OK).
-- - p is a predicate that is used to select only some elements from a context
-- - f is a transformation of an element into a couple element id x element information
computeMap' :: Ord k => ([Element] -> Element -> Bool) -> (Element -> (TEither k, TEither a)) -> Element -> Map k a
computeMap' p f e =
    M.fromList $ rights $ bisequence . f <$> ks
  where
    ks = filterChildren (p $ elChildren e) e

compute :: Element -> TEither BpmnGraph
compute e = do
  let allElements = elChildren e
  pid <- getId e ?# "missing process identifier"
  let ns = filterChildren (pNode allElements) e
  nids <- sequence (getId <$> ns) ?# "missing node identifier"
  let es = filterChildren (pEdge allElements) e
  eids <- sequence (getId <$> es) ?# "missing edge identifier"
  nodeCategories <- computeMap pNode (bcatN allElements) e
  edgeCategories <- computeMap pEdge (bcatE allElements) e
  edgeSources <- computeMap pEdge (bEdgeInfo bsource) e
  edgeTargets <- computeMap pEdge (bEdgeInfo btarget) e
  let nodeNames = computeMap' pNode (bNodeInfo bname) e
  boundaryEventAttachments <- computeMap pBE (bNodeInfo battached) e
  boundaryEventInterrupting <- computeMap pBE (bNodeInfo bisInterrupting) e
  timeEventInformation <- computeMap pTE (bNodeInfo btimeDefinition) e
  let graph =
        BpmnGraph
          ""
          nids -- node ids
          eids -- edge ids
          nodeCategories -- (n, catN(n)) for n in N
          edgeCategories -- (e, catE(n)) for e in E
          edgeSources -- (e, sourceE(e)) for e in E
          edgeTargets -- (e, targetE(e)) for e in E
          nodeNames -- (n, nameN(n)) for n in N
          (M.singleton pid nids) -- (pid, containN(pid))
          (M.singleton pid eids) --- (pid, containE(pid))
          boundaryEventAttachments -- (n, attached(n)) for n in NBE
          [] -- no message inside a (sub-)process
          M.empty -- no message flows inside a (sub-)process
          boundaryEventInterrupting -- (n, isInterrupt(n)) for n in NBE
          timeEventInformation -- (n, timeInformation(n)) for n in NTE
  subProcesses <- e </:* "subProcess"
  subProcessGraphs <- sequence $ compute <$> subProcesses
  pure $ graph <> mconcat subProcessGraphs

bNodeInfo :: (Element -> TEither a) -> Element -> (TEither Node, TEither a)
bNodeInfo f n = (n </. "id", f n)

bEdgeInfo :: (Element -> TEither a) -> Element -> (TEither Edge, TEither a)
bEdgeInfo f e = (e </. "id", f e)

btimeDefinition :: Element -> TEither TimerEventDefinition
btimeDefinition n = Right $ TimerEventDefinition (pTimerDefinitionType n) (pTimerDefinitionValue n)

bisInterrupting :: Element -> TEither Bool
bisInterrupting n = Right $ pCancelActivity n

battached :: Element -> TEither Node
battached n = n </. "attachedToRef"

bsource :: Element -> TEither Node
bsource mf = mf </. "sourceRef"

btarget :: Element -> TEither Node
btarget mf = mf </. "targetRef"

bname :: Element -> TEither String
bname n = n </. "name"

bcatN :: [Element] -> Element -> (TEither Node, TEither NodeType)
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
    f :: Element -> [Element -> Maybe NodeType] -> (TEither Node, TEither NodeType)
    f e' [] = (e' </. "id", Left "unknown node category")
    f e' (p : r) = case p e' of
                      Just t -> (e' </. "id", Right t)
                      Nothing -> f e' r

bcatE :: [Element] -> Element -> (TEither Edge, TEither EdgeType)
bcatE xs e = f e preds
  where
    f :: Element -> [(Element -> Bool, EdgeType)] -> (TEither Edge, TEither EdgeType)
    f e' [] = (e' </. "id", Left "unknown edge category")
    f e' ((p, t) : r) = if p e' then (e' </. "id", Right t) else f e' r
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
