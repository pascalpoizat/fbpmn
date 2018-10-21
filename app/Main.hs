import           Fbpmn
import           Examples                       ( models )
import           Data.Map.Strict                ( keys
                                                , (!?)
                                                )

data Command = Quit          -- quit REPL
             | List          -- list internal examples
             | Show          -- show current graph
             | Import String -- load current graph from internal examples
             | Load String   -- load current graph from JSON and verify file
             | Bpmn String   -- save current graph as BPMN
             | Json String   -- save current graph as JSON
             | Smt String    -- save current graph as SMT
             | Tla String    -- save current graph as TLA+

main :: IO ()
main = repl ("()", Nothing)

{-|
The REPL.
TODO: use State monad.
-}
repl :: (String, Maybe BpmnGraph) -> IO ()
repl (p, g) = do
  putStrLn $ p <> " > "
  rawinput <- getLine
  command  <- parse (words rawinput)
  case command of
    Nothing -> do
      putStrLn "unknown command"
      repl (p, g)
    Just Quit -> putStrLn "goodbye"
    Just Show -> case g of
      Nothing -> do
        putStrLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        print g'
        repl (p, g)
    Just List -> do
      print $ keys models
      repl (p, g)
    Just (Import name) -> case models !? name of
      Nothing -> do
        putStrLn "unknown example"
        repl (p, g)
      Just g' -> do
        putStrLn "example loaded"
        repl (name, Just g')
    Just (Json path) -> case g of
      Nothing -> do
        putStrLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToJSON path g'
        repl (p, g)
    Just (Bpmn path) -> do
      putStrLn "not yet implemented"
      repl (p, g)
    Just (Smt path) -> case g of
      Nothing -> do
        putStrLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToSMT path g'
        repl (p, g)
    Just (Tla path) -> case g of
      Nothing -> do
        putStrLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToTLA path g'
        repl (p, g)
    Just (Load path) -> do
      loadres <- readFromJSON path
      case loadres of
        Nothing -> do
          putStrLn "wrong file"
          repl (p, g)
        Just graph -> if isValidGraph graph
          then do
            putStrLn "graph is correct"
            repl ("(" <> path <> ")", Just graph)
          else do
            putStrLn "graph is incorrect"
            repl (p, g)

parse :: [String] -> IO (Maybe Command)
parse ("quit" : _) = pure $ Just Quit
parse ("show" : _) = pure $ Just Show
parse ("list" : _) = pure $ Just List
parse ["import"  ] = do
  putStrLn "missing example name"
  pure Nothing
parse ["json"] = do
  putStrLn "missing file path"
  pure Nothing
parse ["bpmn"] = do
  putStrLn "missing file path"
  pure Nothing
parse ["smt"] = do
  putStrLn "missing file path"
  pure Nothing
parse ["tla"] = do
  putStrLn "missing file path"
  pure Nothing
parse ["load"] = do
  putStrLn "missing file path"
  pure Nothing
parse ("import" : name : _) = pure $ Just (Import name)
parse ("json"   : path : _) = pure $ Just (Json path)
parse ("bpmn"   : path : _) = pure $ Just (Bpmn path)
parse ("smt"    : path : _) = pure $ Just (Smt path)
parse ("tla"    : path : _) = pure $ Just (Tla path)
parse ("load"   : path : _) = pure $ Just (Load path)
parse _                     = pure Nothing
