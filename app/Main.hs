import           Fbpmn.Model
import           Fbpmn.IO.Bpmn
import           Fbpmn.IO.Json
import           Fbpmn.IO.Smt
import           Fbpmn.IO.Tla
import           Examples                       ( models )
import           Data.Map.Strict                ( keys
                                                , (!?)
                                                )

data Command = Quit        -- quit REPL
             | Help        -- list commands
             | List        -- list internal examples
             | Show        -- show current graph
             | Import Text -- load current graph from internal examples
             | Load Text   -- load current graph from JSON and verify file
             | Bpmn Text   -- load current graph as BPMN
             | Json Text   -- save current graph as JSON
             | Smt Text    -- save current graph as SMT
             | Tla Text    -- save current graph as TLA+

main :: IO ()
main = repl ("()", Nothing)

{-|
The REPL.
TODO: use State monad.
-}
repl :: (Text, Maybe BpmnGraph) -> IO ()
repl (p, g) = do
  putStrLn $ p <> " > "
  rawinput <- getLine
  command  <- parse (words rawinput)
  case command of
    Nothing -> do
      putTextLn "unknown command"
      repl (p, g)
    Just Help -> do
      putTextLn $ unlines
        [ "quit (quit REPL)"
        , "help (list commands)"
        , "list (list internal examples)"
        , "show (show current graph)"
        , "import (load current graph from internal examples)"
        , "load (load current graph from JSON and verify file)"
        , "bpmn (load current graph as BPMN)"
        , "json (save current graph as JSON)"
        , "smt (save current graph as SMT)"
        , "tla (save current graph as TLA)"
        ]
      repl (p, g)
    Just Quit -> putTextLn "goodbye"
    Just Show -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        print g'
        repl (p, g)
    Just List -> do
      print $ keys models
      repl (p, g)
    Just (Import name) -> case models !? name of
      Nothing -> do
        putTextLn "unknown example"
        repl (p, g)
      Just g' -> do
        putTextLn "example loaded"
        repl (name, Just g')
    Just (Json path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToJSON (toString path) g'
        repl (p, g)
    Just (Bpmn path) -> do
      loadres <- readFromBPMN (toString path)
      case loadres of
        Nothing -> do
          putTextLn "wrong file"
          repl (p, g)
        Just graph -> if isValidGraph graph
          then do
            putTextLn "graph is correct"
            repl ("(" <> path <> ")", Just graph)
          else do
            putTextLn "graph is incorrect"
            repl (p, g)
    Just (Smt path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToSMT (toString path) g'
        repl (p, g)
    Just (Tla path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToTLA (toString path) g'
        repl (p, g)
    Just (Load path) -> do
      loadres <- readFromJSON (toString path)
      case loadres of
        Nothing -> do
          putTextLn "wrong file"
          repl (p, g)
        Just graph -> if isValidGraph graph
          then do
            putTextLn "graph is correct"
            repl ("(" <> path <> ")", Just graph)
          else do
            putTextLn "graph is incorrect"
            repl (p, g)

parse :: [Text] -> IO (Maybe Command)
parse ("quit" : _) = pure $ Just Quit
parse ("help" : _) = pure $ Just Help
parse ("show" : _) = pure $ Just Show
parse ("list" : _) = pure $ Just List
parse ["import"  ] = do
  putTextLn "missing example name"
  pure Nothing
parse ["json"] = do
  putTextLn "missing file path"
  pure Nothing
parse ["bpmn"] = do
  putTextLn "missing file path"
  pure Nothing
parse ["smt"] = do
  putTextLn "missing file path"
  pure Nothing
parse ["tla"] = do
  putTextLn "missing file path"
  pure Nothing
parse ["load"] = do
  putTextLn "missing file path"
  pure Nothing
parse ("import" : name : _) = pure $ Just (Import name)
parse ("json"   : path : _) = pure $ Just (Json path)
parse ("bpmn"   : path : _) = pure $ Just (Bpmn path)
parse ("smt"    : path : _) = pure $ Just (Smt path)
parse ("tla"    : path : _) = pure $ Just (Tla path)
parse ("load"   : path : _) = pure $ Just (Load path)
parse _                     = pure Nothing
