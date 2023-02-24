module Fbpmn.Analysis.Tla.IO.Json where

import Data.Aeson (decode)
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.ByteString.Lazy qualified as BS
  ( ByteString,
    readFile,
    writeFile,
  )
import Fbpmn.Analysis.Tla.Model (Log)
import Fbpmn.Helper (FReader (FR), FWriter (FW), TEither, validate)
import Relude
  ( Applicative (pure),
    Either (Left),
    FilePath,
    IO,
    otherwise,
    putTextLn,
    ($),
    (.),
    (<$>),
  )
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )

-- |
-- Generate the JSON representation for a TLA log.
genJSON :: Log -> BS.ByteString
genJSON = encodePretty

-- | FReader from JSON to TLA Log.
reader :: FReader Log
reader = FR readFromJSON ".json"

-- |
-- Read a TLA log from a JSON file.
readFromJSON :: FilePath -> IO (TEither Log)
readFromJSON p = (validate "could not load JSON" . decode <$> BS.readFile p) `catchIOError` handler
  where
    handler :: IOError -> IO (TEither Log)
    handler e
      | isDoesNotExistError e = do
          putTextLn "file not found"
          pure $ Left "file not found"
      | otherwise = do
          putTextLn "unknown error"
          pure $ Left "unknown error"

-- |  FWriter from TLA Log to JSON.
writer :: FWriter Log
writer = FW writeToJSON ".json"

-- |
-- Write a TLA log to a JSON file.
writeToJSON :: FilePath -> Log -> IO ()
writeToJSON p = BS.writeFile p . encodePretty
