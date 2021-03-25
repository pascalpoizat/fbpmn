{-# LANGUAGE OverloadedStrings #-}

module Fbpmn.Analysis.Tla.IO.Log where

import Data.Attoparsec.Text (Parser, anyChar, endOfLine, many1, manyTill, space, string)
import Fbpmn.Analysis.Tla.Model
import Fbpmn.Helper (TEither, FReader (FR), eitherResult, parse, parseContainer, parseIdentifier, parseInteger, parseString, parseTerminal)
import System.IO.Error
  ( IOError,
    catchIOError,
    isDoesNotExistError,
  )

errorLine1 :: Text
errorLine1 = "Error: The following behavior constitutes a counter-example:"

errorLine2 :: Text
errorLine2 = "Error: The behavior up to this point is:"

okLine :: Text
okLine = "Model checking completed. No error has been found."

parseStatus :: Parser Status
parseStatus =
  (string errorLine1 >> return Failure)
    <|> (string errorLine2 >> return Failure)
    <|> (string okLine >> return Success)
    <|> (manyTill anyChar endOfLine *> parseStatus)

parseMapItem :: Parser (Variable, Value)
parseMapItem = do
  var <- parseIdentifier
  _ <- parseTerminal "|->"
  val <- parseValue
  return (var, val)

parseBagItem :: Parser (Value, Value)
parseBagItem = do
  var <- parseValue
  _ <- parseTerminal ":>"
  val <- parseValue
  return (var, val)

parseBag :: Parser [(Value, Value)]
parseBag = parseContainer "(" ")" "@@" parseBagItem

parseMap :: Parser [(Variable, Value)]
parseMap = parseContainer "[" "]" "," parseMapItem

parseTuple :: Parser [Value]
parseTuple = parseContainer "<<" ">>" "," parseValue

parseSet :: Parser [Value]
parseSet = parseContainer "{" "}" "," parseValue

parseValue :: Parser Value
parseValue =
  (SetValue <$> parseSet)
    <|> (TupleValue <$> parseTuple)
    <|> (MapValue . fromList <$> parseMap)
    <|> (BagValue . fromList <$> parseBag)
    <|> (StringValue <$> parseString)
    <|> (IntegerValue <$> parseInteger)
    <|> (VariableValue <$> parseIdentifier)

parseAssignment :: Parser (Variable, Value)
parseAssignment = do
  _ <- parseTerminal "/\\ "
  var <- parseIdentifier
  _ <- parseTerminal "="
  val <- parseValue
  return (var, val)

parseState :: Parser CounterExampleState
parseState = do
  _ <- many space
  sid <- "State " *> parseInteger <* ": "
  info <- manyTill anyChar endOfLine
  assignments <- many parseAssignment
  return $ CounterExampleState sid info (fromList assignments)

parseLog :: Parser Log
parseLog = do
  status <- parseStatus
  case status of
    Success -> return $ Log "log" Nothing Success Nothing
    Failure -> do
      states <- many1 parseState
      return $ Log "log" Nothing Failure $ Just states

readLOG :: FilePath -> IO (TEither Text)
readLOG p = (Right . toText <$> readFile p) `catchIOError` handler
  where
    handler :: IOError -> IO (TEither Text)
    handler e
      | isDoesNotExistError e = do
        putTextLn "file not found"
        pure $ Left "file not found"
      | otherwise = do
        putTextLn "unknown error"
        pure $ Left "unknown error"

-- | FReader from TLA Log file to TLA LOG.
reader :: FReader Log
reader = FR readFromLOG ".log"

readFromLOG :: FilePath -> IO (TEither Log)
readFromLOG p = do
  contents <- readLOG p
  case contents of
    Left err -> pure $ Left err
    Right c -> do
      let result = parse parseLog c
      case eitherResult result of
        Left issue -> do
          putStrLn issue
          pure $ Left . toText $ issue
        Right (Log lid _ ls lcex) ->
          pure $ Right (Log lid (Just model) ls lcex)
          where
            model = takeWhile (/= '.') p <> ".bpmn"
