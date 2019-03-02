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

uri :: Text
uri = "http://www.omg.org/spec/BPMN/20100524/MODEL"

nId :: QName
nId = QName "id" Nothing Nothing

nCollaboration :: QName
nCollaboration = QName "collaboration" (Just $ toString uri) (Just "bpmn")

{-|
An experimental BPMN reading (searches the id of the first collaboration)
-}
decode :: [Content] -> Maybe BpmnGraph
decode cs = do
  c <- listToMaybe
    $ concatMap (findElements nCollaboration) (onlyElems cs)
  n <- findAttr nId c
  Just
    (mkGraph (toText n)
             []
             []
             M.empty
             M.empty
             M.empty
             M.empty
             M.empty
             M.empty
             M.empty
             []
             M.empty
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
