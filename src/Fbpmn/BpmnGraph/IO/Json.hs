module Fbpmn.BpmnGraph.IO.Json where

import Data.Aeson
  ( decode,
  )
import Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy as BS
  ( ByteString,
    readFile,
    writeFile,
  )
import Fbpmn.BpmnGraph.Model
import Fbpmn.Helper (TEither, FReader (FR), FWriter (FW), validate)
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )

-- |
-- Generate the JSON representation for a BPMN Graph.
genJSON :: BpmnGraph -> BS.ByteString
genJSON = encodePretty

-- | FReader from JSON to BPMN Graph.
reader :: FReader BpmnGraph
reader = FR readFromJSON ".json" 

-- |
-- Read a BPMN Graph from a JSON file.
readFromJSON :: FilePath -> IO (TEither BpmnGraph)
readFromJSON p = (validate "could not load JSON" . decode <$> BS.readFile p) `catchIOError` handler
  where
    handler :: IOError -> IO (TEither BpmnGraph)
    handler e
      | isDoesNotExistError e = do
        putTextLn "file not found"
        pure $ Left "file not found"
      | otherwise = do
        putTextLn "unknown error"
        pure $ Left "unknown error"

-- | FWriter from BPMN Graph to JSON.
writer :: FWriter BpmnGraph
writer = FW writeToJSON ".json"

-- |
-- Write a BPMN Graph to a JSON file.
writeToJSON :: FilePath -> BpmnGraph -> IO ()
writeToJSON p = BS.writeFile p . encodePretty
