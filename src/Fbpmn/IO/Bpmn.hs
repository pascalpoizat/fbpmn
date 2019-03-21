module Fbpmn.IO.Bpmn where

import           Fbpmn.Helper                   ( tlift2 )
import           Fbpmn.Model
import           Text.XML.Light                 ( Element(..)
                                                , Content(..)
                                                , QName(..)
                                                , elChildren
                                                , findAttr
                                                , findChildren
                                                , findChildren
                                                , filterChildren
                                                , parseXML
                                                , onlyElems
                                                )
import qualified Data.Map                      as M
                                                ( empty
                                                , fromList
                                                , singleton
                                                )
import qualified Data.ByteString.Lazy          as BS
                                                ( readFile )
import           System.IO.Error                ( IOError
                                                , catchIOError
                                                , isDoesNotExistError
                                                )

--
-- helpers for building QNames
--

uri :: String
uri = "http://www.omg.org/spec/BPMN/20100524/MODEL"

nA :: String -> QName
nA s = QName s Nothing Nothing

nE :: String -> QName
nE s = QName s (Just uri) (Just "bpmn")

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
oneMaybeOf e ps = not . null . (filter isJust) $ ps <*> [e]

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

isIdOf' :: String -> Element -> Bool
isIdOf' s e = fromMaybe False $ isIdOf s e

findById :: [Element] -> String -> Maybe Element
findById es eid = do
  ess <- nonEmpty [ e | e <- es, isIdOf' eid e ]
  Just $ head ess

findByIds :: [Element] -> [String] -> [Element]
findByIds es ids = [ e | e <- es, eid <- ids, isIdOf' eid e ]

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
  _            -> True -- cancelActivity by default

-- start events
-- NSE or MSE
-- other start events are assimilated to NSE
pSE :: [Element] -> Element -> Bool
pSE _ = (?=) "startEvent"
pMSE :: [Element] -> Element -> Maybe NodeType
pMSE es e = if pSE es e && pMx e then Just MessageStartEvent else Nothing
pNSE :: [Element] -> Element -> Maybe NodeType
pNSE es e =
  if pSE es e && (isNothing . pMSE es $ e) then Just NoneStartEvent else Nothing

-- intermediary events
-- CMIE or TMIE
-- other intermediary events are discarded
pITE :: [Element] -> Element -> Bool
pITE _ = (?=) "intermediateThrowEvent"
pTMIE :: [Element] -> Element -> Maybe NodeType
pTMIE es e = if pITE es e && pMx e then Just ThrowMessageIntermediateEvent else Nothing
pICE :: [Element] -> Element -> Bool
pICE _ = (?=) "intermediateCatchEvent"
pCMIE :: [Element] -> Element -> Maybe NodeType
pCMIE es e = if pICE es e && pMx e then Just CatchMessageIntermediateEvent else Nothing
pIE :: [Element] -> Element -> Bool
pIE es e = e `oneMaybeOf` [pTMIE es, pCMIE es]

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
pNEE es e = if pEE es e && not (e `oneMaybeOf` [pMEE es, pTEE es])
  then Just NoneEndEvent
  else Nothing

-- boundary events
-- MBE (default is interrupting, i.e., cancelActivity=true if not given)
-- other boundary events are discarded
pBE :: [Element] -> Element -> Bool
pBE _ = (?=) "boundaryEvent"
pMBE :: [Element] -> Element -> Maybe NodeType
pMBE es e =
  if pBE es e && pMx e then Just $ MessageBoundaryEvent (pIx e) else Nothing

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
    `oneMaybeOf` [ pAndGateway es
                 , pOrGateway es
                 , pXorGateway es
                 , pEventBasedGateway es
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
pAsAT es e = if e `oneOf` ([pAT, pUT, pWT, pXT, pBT, pMT] <*> [es])
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
  sa  <- findAttr (nA "sourceRef") e
  sn  <- findById es sa
  def <- findAttr (nA "default") sn
  pure $ pSF es e && isIdOf' def e

pNSF :: [Element] -> Element -> Bool
pNSF es e = pSF es e && not (e `oneOf` [pCSF es, pDSF es])
pEdge :: [Element] -> Element -> Bool
pEdge es e = e `oneOf` [pSF es, pMF es]

{-|
An experimental BPMN reading.

Requirements:
- collaboration has a name
- message flows have a name (used as message type)

Enhancements:
- remove duplicates in cMessageTypes
-}
decode :: [Content] -> Maybe BpmnGraph
decode cs = do
  -- top-level elements
  topElements      <- pure $ onlyElems cs
  -- collaboration (1st one to be found)
  c <- listToMaybe $ concatMap (findChildren (nE "collaboration")) topElements
  cId              <- getId c
  -- participants
  cParticipants    <- pure $ findChildren (nE "participant") c
  cParticipantRefs <- sequence $ findAttr (nA "processRef") <$> cParticipants
  -- cParticipantIds <- sequence $ getId <$> cParticipants
  -- processes
  allProcesses     <- pure $ concatMap (findChildren (nE "process")) topElements
  cProcesses       <- pure $ findByIds allProcesses cParticipantRefs
  -- message flows and messages
  cMessageFlows    <- pure $ findChildren (nE "messageFlow") c
  cMessageFlowIds  <- sequence $ getId <$> cMessageFlows
  cMessageTypes    <- sequence $ nameOrElseId <$> cMessageFlows
  -- high level information (collaboration level)
  g                <- pure $ BpmnGraph
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
    cMessageTypes
    (M.fromList $ catMaybes $ tlift2 . bname <$> cMessageFlows)
  -- compute for participant processes
  processGraphs <- sequence $ compute <$> cProcesses
  pure $ g <> mconcat processGraphs
 where
  ccatE :: String -> (Edge, EdgeType)
  ccatE e = (e, MessageFlow)
  ccatN :: String -> (Node, NodeType)
  ccatN e = (e, Process)

compute :: Element -> Maybe BpmnGraph
compute e = do
  allElements <- pure $ elChildren e
  pid         <- getId e
  ns          <- pure $ filterChildren (pNode allElements) e
  nids        <- sequence $ getId <$> ns
  es          <- pure $ filterChildren (pEdge allElements) e
  eids        <- sequence $ getId <$> es
  sps         <- pure $ findChildren (nE "subProcess") e
  g           <- pure $ BpmnGraph
    ""
    nids
    eids
    (M.fromList $ catMaybes $ tlift2 . bcatN allElements <$> ns)
    (M.fromList $ catMaybes $ tlift2 . bcatE allElements <$> es)
    (M.fromList $ catMaybes $ tlift2 . bsource <$> es)
    (M.fromList $ catMaybes $ tlift2 . btarget <$> es)
    (M.fromList $ catMaybes $ tlift2 . bname <$> ns)
    (M.singleton pid nids)
    (M.singleton pid eids)
    []
    M.empty
  spgs <- sequence $ compute <$> sps
  pure $ g <> mconcat spgs

bsource :: Element -> (Maybe Edge, Maybe Node)
bsource mf = (getId mf, findAttr (nA "sourceRef") mf)

btarget :: Element -> (Maybe Edge, Maybe Node)
btarget mf = (getId mf, findAttr (nA "targetRef") mf)

bname :: Element -> (Maybe Edge, Maybe String)
bname mf = (getId mf, getName mf)

bcatN :: [Element] -> Element -> (Maybe Node, Maybe NodeType)
bcatN xs e = f e preds
 where
  preds = [pNSE, pMSE
          ,pCMIE, pTMIE
          ,pMBE
          ,pNEE, pMEE, pTEE
          ,pAndGateway, pXorGateway, pOrGateway, pEventBasedGateway
          ,pST, pRT, pAsAT
          ,pSP] <*> [xs]
  f :: Element -> [Element -> Maybe NodeType] -> (Maybe Node, Maybe NodeType)
  f e' []      = (getId e', Nothing)
  f e' (p : r) = if isJust res then (getId e', res) else f e' r
    where
      res = p e'

bcatE :: [Element] -> Element -> (Maybe Edge, Maybe EdgeType)
bcatE xs e = f e preds
 where
  f :: Element -> [(Element -> Bool, EdgeType)] -> (Maybe Edge, Maybe EdgeType)
  f e' ((p, t) : r) = if p e' then (getId e', Just t) else f e' r
  f e' []           = (getId e', Nothing)
  -- in preds, the order is important since a DSF validates pNSF
  preds =
    [ (pDSF xs, DefaultSequenceFlow)
    , (pCSF xs, ConditionalSequenceFlow)
    , (pNSF xs, NormalSequenceFlow)
    , (pMF xs , MessageFlow)
    ]

{-|
Read a BPMN Graph from a BPMN file.
-}
readFromBPMN :: FilePath -> IO (Maybe BpmnGraph)
readFromBPMN p = (decode . parseXML <$> BS.readFile p) `catchIOError` handler
 where
  handler :: IOError -> IO (Maybe BpmnGraph)
  handler e
    | isDoesNotExistError e = do
      putTextLn "file not found"
      pure Nothing
    | otherwise = do
      putTextLn "unknown error"
      pure Nothing
