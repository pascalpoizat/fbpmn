module Fbpmn.IO.Bpmn where

import           Fbpmn.Helper                   ( tlift2 )
import           Fbpmn.Model
import           Text.XML.Light                 ( Element(..)
                                                , Content(..)
                                                , QName(..)
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
findById es eid = listToMaybe $ concatMap (filterChildren (eid `isIdOf'`)) es

findByIds :: [Element] -> [String] -> [Element]
findByIds es ids = [e | e <- es, eid <- ids, isIdOf' eid e]

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

-- start events
-- NSE or MSE
-- other start events are assimilated to NSE
pSE :: [Element] -> Element -> Bool
pSE _ = (?=) "startEvent"
pMSE :: [Element] -> Element -> Bool
pMSE es e = pSE es e && pMx e
pNSE :: [Element] -> Element -> Bool
pNSE es e = pSE es e && (not . (pMSE es) $ e)

-- intermediary events
-- CMIE or TMIE
-- other intermediary events are discarded
pITE :: [Element] -> Element -> Bool
pITE _ = (?=) "intermediateThrowEent"
pTMIE :: [Element] -> Element -> Bool
pTMIE es e = pITE es e && pMx e
pICE :: [Element] -> Element -> Bool
pICE _ = (?=) "intermediateCatchEvent"
pCMIE :: [Element] -> Element -> Bool
pCMIE es e = pICE es e && pMx e
pIE :: [Element] -> Element -> Bool
pIE es e = e `oneOf` [pTMIE es, pCMIE es]

-- end events
-- NEE, MEE, or TEE
-- other end events are assimilated to NEE
pEE :: [Element] -> Element -> Bool
pEE _ = (?=) "endEvent"
pMEE :: [Element] -> Element -> Bool
pMEE es e = pEE es e && pMx e
pTEE :: [Element] -> Element -> Bool
pTEE es e = pSE es e && pTx e
pNEE :: [Element] -> Element -> Bool
pNEE es e = pEE es e && (not $ e `oneOf` [pMEE es, pTEE es])

-- events
pE :: [Element] -> Element -> Bool
pE es e = e `oneOf` [pSE es, pIE es, pEE es]

-- gateways
pAndGateway :: [Element] -> Element -> Bool
pAndGateway _ = (?=) "parallelGateway"
pOrGateway :: [Element] -> Element -> Bool
pOrGateway _ = (?=) "inclusiveGateway"
pXorGateway :: [Element] -> Element -> Bool
pEventBasedGateway _ = (?=) "exclusiveGateway"
pEventBasedGateway :: [Element] -> Element -> Bool
pXorGateway _ = (?=) "eventBasedGateway"
pGateway :: [Element] -> Element -> Bool
pGateway es e =
  e
    `oneOf` [ pAndGateway es
            , pOrGateway es
            , pXorGateway es
            , pEventBasedGateway es
            ]

-- tasks
-- AT, ST, or RT
-- other tasks are discarded
pST :: [Element] -> Element -> Bool
pST _ = (?=) "sendTask"
pRT :: [Element] -> Element -> Bool
pRT _ = (?=) "receiveTask"
pAT :: [Element] -> Element -> Bool
pAT _ = (?=) "task"
pT :: [Element] -> Element -> Bool
pT es e = e `oneOf` [pAT es, pST es, pRT es]

-- activities
pSP :: [Element] -> Element -> Bool
pSP _ = (?=) "subProcess"
pA :: [Element] -> Element -> Bool
pA es e = e `oneOf` [pT es, pSP es]

-- processes
pP :: [Element] -> Element -> Bool
pP _ = (?=) "process"

-- nodes
pNode :: [Element] -> Element -> Bool
pNode es e = e `oneOf` [pE es, pGateway es, pA es, pP es]

-- edges
-- sequence flows are NSF, CSF or DSF
pMF :: [Element] -> Element -> Bool
pMF _ = (?=) "messageFlow"
pSF :: [Element] -> Element -> Bool
pSF _ = (?=) "sequenceFlow"
pCSF :: [Element] -> Element -> Bool
pCSF es e = pSF es e && pCx e
-- for e to be a DSF it is a bit more complicated
-- 1. e.name = sequenceFlow 
-- 2. e.sourceRef.default = e.id
pDSF :: [Element] -> Element -> Bool
pDSF es e = fromMaybe False $ do
  eid <- getId e
  sa  <- findAttr (nA "sourceRef") e
  sn  <- findById es sa
  def <- findAttr (nA "default") sn
  pure $ pSF es e && (def == eid)

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
    -- all elements
  allElements      <- pure $ onlyElems cs
  -- collaboration (1st one to be found)
  c <- listToMaybe $ concatMap (findChildren (nE "collaboration")) allElements
  cId              <- getId c
  -- participants
  cParticipants    <- pure $ findChildren (nE "participant") c
  cParticipantRefs <- sequence $ findAttr (nA "processRef") <$> cParticipants
  cParticipantIds <- sequence $ getId <$> cParticipants
  -- processes
  allProcesses     <- pure $ concatMap (findChildren (nE "process")) allElements
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
  processGraphs <- sequence $ compute allElements <$> cProcesses
  pure $ g <> mconcat processGraphs
 where
  ccatE :: String -> (Edge, EdgeType)
  ccatE e = (e, MessageFlow)
  ccatN :: String -> (Node, NodeType)
  ccatN e = (e, Process)

compute :: [Element] -> Element -> Maybe BpmnGraph
compute allElements e = do
  pid  <- getId e
  ns   <- pure $ filterChildren (pNode allElements) e
  nids <- sequence $ getId <$> ns
  es   <- pure $ filterChildren (pEdge allElements) e
  eids <- sequence $ getId <$> es
  sps  <- pure $ findChildren (nE "subProcess") e
  g    <- pure $ BpmnGraph ""
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
  spgs <- sequence $ compute allElements <$> sps
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
    f :: Element -> [(Element -> Bool, NodeType)] -> (Maybe Node, Maybe NodeType)
    f e' ((p, t):r) = if p e' then (getId e', Just t) else f e' r
    f e' [] = (getId e', Nothing)
    preds = [(pNSE xs, NoneStartEvent)
            ,(pMSE xs, MessageStartEvent)
            ,(pCMIE xs, CatchMessageIntermediateEvent)
            ,(pTMIE xs, ThrowMessageIntermediateEvent)
            ,(pNEE xs, NoneEndEvent)
            ,(pMEE xs, MessageEndEvent)
            ,(pTEE xs, TerminateEndEvent)
            ,(pAndGateway xs, AndGateway)
            ,(pXorGateway xs, XorGateway)
            ,(pOrGateway xs, OrGateway)
            ,(pEventBasedGateway xs, EventBasedGateway)
            ,(pST xs, SendTask)
            ,(pRT xs, ReceiveTask)
            ,(pAT xs, AbstractTask)
            ,(pSP xs, SubProcess)
            ]

bcatE :: [Element] -> Element -> (Maybe Edge, Maybe EdgeType)
bcatE xs e = f e preds
  where
    f :: Element -> [(Element -> Bool, EdgeType)] -> (Maybe Edge, Maybe EdgeType)
    f e' ((p, t):r) = if p e' then (getId e', Just t) else f e' r
    f e' [] = (getId e', Nothing)
    preds = [(pNSF xs, NormalSequenceFlow)
            ,(pCSF xs, ConditionalSequenceFlow)
            ,(pDSF xs, DefaultSequenceFlow)
            ,(pMF xs, MessageFlow)]

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
