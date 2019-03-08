module Fbpmn.IO.Json where

import           Fbpmn.Model
import qualified Data.ByteString.Lazy          as BS
                                                ( ByteString
                                                , writeFile
                                                , readFile
                                                )
import           Data.Aeson                     ( decode
                                                )
import           Data.Aeson.Encode.Pretty       ( encodePretty )
import           System.IO.Error                ( IOError
                                                , catchIOError
                                                , isDoesNotExistError
                                                )

{-|
Generate the JSON representation for a BPMN Graph.
-}
genJSON :: BpmnGraph -> BS.ByteString
genJSON = encodePretty

{-|
Read a BPMN Graph from a JSON file.
-}
readFromJSON :: FilePath -> IO (Maybe BpmnGraph)
readFromJSON p = (decode <$> BS.readFile p) `catchIOError` handler
 where

  handler :: IOError -> IO (Maybe BpmnGraph)
  handler e
    | isDoesNotExistError e = do
      putTextLn "file not found"
      pure Nothing
    | otherwise = do
      putTextLn "unknown error"
      pure Nothing

{-|
Write a BPMN Graph to a JSON file.
-}
writeToJSON :: FilePath -> BpmnGraph -> IO ()
writeToJSON p = BS.writeFile p . encodePretty
