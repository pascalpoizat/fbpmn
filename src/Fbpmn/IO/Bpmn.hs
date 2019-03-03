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

nId :: QName
nId = nA "id"

nName :: QName
nName = nA "name"

nCollaboration :: QName
nCollaboration = nE "collaboration"

nParticipant :: QName
nParticipant = nE "participant"

nMessageFlow :: QName
nMessageFlow = nE "messageFlow"

{-|
An experimental BPMN reading.

Enhancements:
- remove duplicate message flow names
- use messages instance of message flow names (if available)
-}
decode :: [Content] -> Maybe BpmnGraph
decode cs = do
  es <- pure $ onlyElems cs
  c  <- listToMaybe $ concatMap (findElements nCollaboration) es
  n  <- findAttr nId c
  ps <- pure $ findElements nParticipant c
  mfs <- pure $ findElements nMessageFlow c
  ms <- sequence $ findAttr nName <$> mfs
  Just
    (mkGraph (toText n)
             [] -- TODO:
             [] -- TODO:
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
