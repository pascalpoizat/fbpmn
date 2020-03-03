{-# LANGUAGE OverloadedStrings #-}
module Fbpmn.Analysis.Tla.IO.Log where

import           Fbpmn.Analysis.Tla.Model
import           Data.Attoparsec.Text           (Parser, anyChar, manyTill, space, sepBy, parse, many1, eitherResult, endOfLine, decimal, char, digit, letter, string)
import           System.IO.Error                ( IOError
                                                , catchIOError
                                                , isDoesNotExistError
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

parseTerminal :: Text -> Parser ()
parseTerminal sep = do
  _ <- many space
  _ <- string sep
  return ()

parseMapItem :: Parser (Variable, Value)
parseMapItem = do
  var <- parseVariable
  _ <- parseTerminal "|->"
  val <- parseValue
  return (var, val)

parseBagItem :: Parser (Value, Value)
parseBagItem = do
  var <- parseValue
  _ <- parseTerminal ":>"
  val <- parseValue
  return (var, val)

parseContainer :: Text -> Text -> Text -> Parser a -> Parser [a]
parseContainer beg end sep item = do
  _ <- parseTerminal beg
  items <- sepBy item $ parseTerminal sep
  _ <- parseTerminal end
  return items

parseBag :: Parser [(Value, Value)]
parseBag = parseContainer "(" ")" "@@" parseBagItem

parseMap :: Parser [(Variable, Value)]
parseMap = parseContainer "[" "]" "," parseMapItem

parseTuple :: Parser [Value]
parseTuple = parseContainer "<<" ">>" "," parseValue

parseSet :: Parser [Value]
parseSet = parseContainer "{" "}" "," parseValue

parseValue :: Parser Value
parseValue = (SetValue <$> parseSet) 
  <|> (TupleValue <$> parseTuple)
  <|> (MapValue . fromList <$> parseMap)
  <|> (BagValue . fromList <$> parseBag)
  <|> (StringValue <$> parseString)
  <|> (IntegerValue <$> parseInteger)
  <|> (VariableValue <$> parseVariable)

parseAssignment :: Parser (Variable, Value)
parseAssignment = do
  _ <- parseTerminal "/\\ "
  var <- parseVariable
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

readLOG :: FilePath -> IO (Maybe Text)
readLOG p = (Just . fromString <$> readFile p) `catchIOError` handler
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
