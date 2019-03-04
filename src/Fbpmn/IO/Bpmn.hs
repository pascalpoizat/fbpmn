module Fbpmn.IO.Bpmn where

import           Fbpmn.Model
import           Text.XML.Light
import qualified Data.Map                      as M
                                                ( empty )
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

getId :: Element -> Maybe String
getId e = findAttr (nA "id") e

-- for the time being all start events are treated as NSE
-- (in the BPMN loading only, it is correct in the JSON loading)
pSE :: QName -> Bool
pSE = (== nE "startEvent")

-- for the time being all end events are treated as NEE
-- (in the BPMN loading only, it is correct in the JSON loading)
pEE :: QName -> Bool
pEE = (== nE "endEvent")

pOR :: QName -> Bool
pOR = (== nE "inclusiveGateway")

pAND :: QName -> Bool
pAND = (== nE "parallelGateway")

pXOR :: QName -> Bool
pXOR = (== nE "exclusiveGateway")

pG :: QName -> Bool
pG q = pOR q || pAND q || pXOR q

pST :: QName -> Bool
pST = (== nE "sendTask")

pRT :: QName -> Bool
pRT = (== nE "receiveTask")

pAT :: QName -> Bool
pAT = (== nE "task")

pT :: QName -> Bool
pT q = pAT q || pST q || pRT q

pN :: QName -> Bool
pN q = pT q || pSE q || pEE q || pG q

pMF :: QName -> Bool
pMF = (== nE "messageFlow")

pSF :: QName -> Bool
pSF = (== nE "sequenceFlow")

pE :: QName -> Bool
pE q = pMF q || pSF q

{-|
An experimental BPMN reading.

Enhancements:
- remove duplicate message flow names
- use messages instance of message flow names (if available)
-}
decode :: [Content] -> Maybe BpmnGraph
decode cs = do
  elems <- pure $ onlyElems cs
  c  <- listToMaybe $ concatMap (findElements (nE "collaboration")) elems
  ns <- pure $ concatMap (filterElementsName pN) elems
  es <- pure $ concatMap (filterElementsName pE) elems
  name  <- getId c
  -- ps <- pure $ findElements (nE "participant") c
  mfs <- pure $ filterElementsName pMF c
  ms <- sequence $ findAttr (nA "name") <$> mfs
  Just
    (mkGraph (toText name)
             (catMaybes $ getId <$> ns) -- TODO: missing process nodes
             (catMaybes $ getId <$> es)
             M.empty -- TODO:
             M.empty -- TODO:
             M.empty -- TODO:
             M.empty -- TODO:
             M.empty -- TODO:
             M.empty -- TODO:
             M.empty -- TODO:
             ms
             M.empty -- TODO:
    )

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
