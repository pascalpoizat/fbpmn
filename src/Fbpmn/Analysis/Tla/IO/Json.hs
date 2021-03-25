module Fbpmn.Analysis.Tla.IO.Json where

import           Data.Aeson               (decode)
import           Data.Aeson.Encode.Pretty (encodePretty)
import qualified Data.ByteString.Lazy     as BS (ByteString, readFile,
                                                 writeFile)
import           Fbpmn.Analysis.Tla.Model
import           System.IO.Error          (IOError, catchIOError,
                                           isDoesNotExistError)

{-|
Generate the JSON representation for a TLA log.
-}
genJSON :: Log -> BS.ByteString
genJSON = encodePretty

{-|
Read a TLA log from a JSON file.
-}
readFromJSON :: FilePath -> IO (Maybe Log)
readFromJSON p = (decode <$> BS.readFile p) `catchIOError` handler
 where

  handler :: IOError -> IO (Maybe Log)
  handler e
    | isDoesNotExistError e = do
      putTextLn "file not found"
      pure Nothing
    | otherwise = do
      putTextLn "unknown error"
      pure Nothing

{-|
Write a TLA log to a JSON file.
-}
writeToJSON :: FilePath -> Log -> IO ()
writeToJSON p = BS.writeFile p . encodePretty
