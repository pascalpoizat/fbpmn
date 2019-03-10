module Fbpmn.IO.Bpmn where

import           Fbpmn.Model
import           Text.XML.Light                 ( Element(..)
                                                , Content(..)
                                                , QName(..)
                                                , findAttr
                                                , findChildren
                                                , findChildren
                                                , filterChildrenName
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

uri :: String
uri = "http://www.omg.org/spec/BPMN/20100524/MODEL"

nA :: String -> QName
nA s = QName s Nothing Nothing

nE :: String -> QName
nE s = QName s (Just uri) (Just "bpmn")

(?=) :: String -> Element -> Bool
(?=) s = (==) (nE s) . elName

oneOf :: Element -> [Element -> Bool] -> Bool
oneOf e ps = getAny . foldMap Any $ ps <*> [e]

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

nameOrElseId :: Element -> Maybe String
nameOrElseId = aOrElseB "name" "id"

idOrNothing :: Element -> Maybe String
idOrNothing = findAttr (nA "id")

hasChildren :: QName -> Element -> Bool
hasChildren q = not . null . findChildren q

-- message events
pMx :: Element -> Bool
pMx = hasChildren (nE "messageEventDefinition")
pTx :: Element -> Bool
pTx = hasChildren (nE "terminateEventDefinition")

-- start events
-- NSE or MSE
-- other start events are assimilated to NSE
pSE :: Element -> Bool
pSE = (?=) "startEvent"
pMSE :: Element -> Bool
pMSE e = pSE e && pMx e
pNSE :: Element -> Bool
pNSE e = pSE e && (not . pMSE $ e)

-- intermediary events
-- CMIE or TMIE
-- other intermediary events are discarded
pITE :: Element -> Bool
pITE = (?=) "intermediateThrowEent"
pTMIE :: Element -> Bool
pTMIE e = pITE e && pMx e
pICE :: Element -> Bool
pICE = (?=) "intermediateCatchEvent"
pCMIE :: Element -> Bool
pCMIE e = pICE e && pMx e
pIE e = e `oneOf` [pTMIE, pCMIE]

-- end events
-- NEE, MEE, or TEE
-- other end events are assimilated to NEE
pEE :: Element -> Bool
pEE = (?=) "endEvent"
pMEE :: Element -> Bool
pMEE e = pEE e && pMx e
pTEE :: Element -> Bool
pTEE e = pSE e && pTx e
pNEE :: Element -> Bool
pNEE e = not $ e `oneOf` [pMEE, pTEE] 

-- events
pE :: Element -> Bool
pE e = e `oneOf` [pSE, pIE, pEE]

-- gateways
pAndGateway :: Element -> Bool
pAndGateway = (?=) "parallelGateway"
pOrGateway :: Element -> Bool
pOrGateway = (?=) "inclusiveGateway"
pXorGateway :: Element -> Bool
pEventBasedGateway = (?=) "exclusiveGateway"
pEventBasedGateway :: Element -> Bool
pXorGateway = (?=) "eventBasedGateway"
pGateway :: Element -> Bool
pGateway e =
  e `oneOf` [pAndGateway, pOrGateway, pXorGateway, pEventBasedGateway]

-- tasks
-- AT, ST, or RT
-- other tasks are discarded
pST :: Element -> Bool
pST = (?=) "sendTask"
pRT :: Element -> Bool
pRT = (?=) "receiveTask"
pAT :: Element -> Bool
pAT = (?=) "task"
pT e = e `oneOf` [pAT, pST, pRT]

-- activities
pSP :: Element -> Bool
pSP = (?=) "subProcess"
pA :: Element -> Bool
pA e = e `oneOf` [pT, pSP]

-- processes
pP = (?=) "process"

-- nodes
pNode :: Element -> Bool
pNode e = e `oneOf` [pE, pGateway, pA, pP]

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
    allElements <- pure $ onlyElems cs
    -- collaboration (1st one to be found)
    c <- listToMaybe $ concatMap (findChildren (nE "collaboration")) allElements
    cName <- findAttr (nA "id") c
    -- participants
    cParticipants <- pure $ findChildren (nE "participant") c
    cParticipantRefs <- sequence $ findAttr (nA "processRef") <$> cParticipants
    cParticipantNames <- sequence $ aOrElseB "name" "processRef" <$> cParticipants
    -- processes
    allProcesses <- pure $ concatMap (findChildren (nE "process")) allElements
    cProcesses <- pure $ filter (filterByReferences cParticipantRefs) allProcesses 
    -- message flows and messages
    cMessageFlows <- pure $ findChildren (nE "messageFlow") c
    cMessageFlowIds <- sequence $ idOrNothing <$> cMessageFlows
    cMessageTypes <- sequence $ nameOrElseId <$> cMessageFlows
    -- graph
    Just (mkGraph
          (toText cName)
          cParticipantNames -- TODO: completer avec tous les nodes
          cMessageFlowIds -- TODO: completer avec tous les edges
          M.empty -- TODO:
          M.empty -- TODO:
          M.empty -- TODO:
          M.empty -- TODO:
          M.empty -- TODO:
          M.empty -- TODO:
          M.empty -- TODO:
          cMessageTypes
          M.empty -- TODO:
          )
    where
      filterByReferences = undefined 

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
