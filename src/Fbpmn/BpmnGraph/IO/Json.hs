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
import Fbpmn.Helper (validate)
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )

-- |
-- Generate the JSON representation for a BPMN Graph.
genJSON :: BpmnGraph -> BS.ByteString
genJSON = encodePretty

-- |
-- Read a BPMN Graph from a JSON file.
readFromJSON :: FilePath -> Maybe a -> IO (Either Text BpmnGraph)
readFromJSON p _ = (validate "could not load JSON" . decode <$> BS.readFile p) `catchIOError` handler
  where
    handler :: IOError -> IO (Either Text BpmnGraph)
    handler e
      | isDoesNotExistError e = do
        putTextLn "file not found"
        pure $ Left "file not found"
      | otherwise = do
        putTextLn "unknown error"
        pure $ Left "unknown error"

-- |
-- Write a BPMN Graph to a JSON file.
writeToJSON :: FilePath -> Maybe a -> BpmnGraph -> IO ()
writeToJSON p _ = BS.writeFile p . encodePretty
