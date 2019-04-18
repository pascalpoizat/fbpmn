{-# LANGUAGE OverloadedStrings #-}
module Fbpmn.Analysis.Tla.IO.Log where

import           Fbpmn.Analysis.Tla.Model
import           Data.Attoparsec.Text           (Parser, anyChar, manyTill, space, sepBy, parse, many1, eitherResult, endOfLine, decimal, char, digit, letter, string)
import           System.IO.Error                ( IOError
                                                , catchIOError
                                                , isDoesNotExistError
                                                )

errorLine :: Text
errorLine = "Error: The following behavior constitutes a counter-example:"

okLine :: Text
okLine = "Model checking completed. No error has been found."

parseStatus :: Parser Status
parseStatus =
  (string errorLine >> return Failure)
    <|> (string okLine >> return Success)
    <|> (manyTill anyChar endOfLine *> parseStatus)

parseVariable :: Parser Variable
parseVariable = do
  _ <- many space
  car1 <- letter <|> char '_'
  rest <- many (letter <|> digit <|> char '_')
  return $ [car1] <> rest

parseString :: Parser String
parseString = many space *> "\"" *> manyTill anyChar "\""

parseInteger :: Parser Integer
parseInteger = many space *> decimal

parseMapItem :: Parser (Variable, Value)
parseMapItem = do
  _ <- many space
  var <- parseVariable
  _ <- many space
  _ <- "|->"
  _ <- many space
  val <- parseValue
  return (var, val)

parseBagItem :: Parser (Value, Value)
parseBagItem = do
  _ <- many space
  var <- parseValue
  _ <- many space
  _ <- ":>"
  _ <- many space
  val <- parseValue
  return (var, val)

parseBag :: Parser [(Value, Value)]
parseBag = do
  _ <- many space
  _ <- "("
  _ <- many space
  items <- sepBy parseBagItem (many space *> "@@" *> many space)
  _ <- many space
  _ <- ")"
  return items

parseMap :: Parser [(Variable, Value)]
parseMap = do
  _ <- many space
  _ <- "["
  _ <- many space
  items <- sepBy parseMapItem (many space *> "," *> many space)
  _ <- many space
  _ <- "]"
  return items
  
parseTuple :: Parser [Value]
parseTuple = do
  _ <- many space
  _ <- "<<"
  _ <- many space
  items <- sepBy parseValue (many space *> "," *> many space)
  _ <- many space
  _ <- ">>"
  return items

parseValue :: Parser Value
parseValue = (TupleValue <$> parseTuple)
  <|> (MapValue . fromList <$> parseMap)
  <|> (BagValue . fromList <$> parseBag)
  <|> (StringValue <$> parseString)
  <|> (IntegerValue <$> parseInteger)
  <|> (VariableValue <$> parseVariable)

parseAssignment :: Parser (Variable, Value)
parseAssignment = do
  _ <- many space
  _ <- "/\\ "
  var <- parseVariable
  _ <- many space
  _ <- "="
  _ <- many space
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

readLOG :: FilePath -> IO (Maybe Text)
readLOG p = (Just <$> readFile p) `catchIOError` handler
 where

  handler :: IOError -> IO (Maybe Text)
  handler e
    | isDoesNotExistError e = do
      putTextLn "file not found"
      pure Nothing
    | otherwise = do
      putTextLn "unknown error"
      pure Nothing

readFromLOG :: FilePath -> Maybe String -> IO (Maybe Log)
readFromLOG p _ = do
  contents <- readLOG p
  case contents of
    Nothing -> pure Nothing
    Just c  -> do
      result <- pure $ parse parseLog c
      case eitherResult result of
        Left issue -> do
          putStrLn $ "parsing error: " <> issue
          return Nothing
        Right (Log lid _ ls lcex) ->
          pure $ Just (Log lid (Just model) ls lcex)
          where
            model = takeWhile (not . (== '.')) p <> ".bpmn"
