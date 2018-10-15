import           Fbpmn
import           Examples                       ( g1 )
import           Data.Map.Strict                ( keys )

data Command = Quit       -- quit REPL
             | List       -- list internal examples
             | Load Text  -- load and verify file
             | Show       -- show current graph
             | Bpmn Text  -- save current graph as BPMN
             | Smt Text   -- save current graph as SMT

examples :: Map Text BpmnGraph
examples = fromList [("g1", g1)]

main :: IO ()
main = repl ("()", Nothing)

repl :: (Text, Maybe BpmnGraph) -> IO ()
repl (p, g) = do
  putTextLn $ p <> " > "
  rawinput <- getLine
  command  <- parse (words rawinput)
  case command of
    Nothing -> do
      putTextLn "unknown command"
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
      print $ keys examples
      repl (p, g)
    Just (Bpmn path) -> do
      putTextLn "not yet implemented"
      repl (p, g)
    Just (Smt path) -> do
      putTextLn "not yet implemented"
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
            repl $ ("(" <> path <> ")", Just graph)
          else do
            putTextLn "graph is incorrect"
            repl (p, g)

parse :: [Text] -> IO (Maybe Command)
parse ("quit" : _) = pure $ Just Quit
parse ("show" : _) = pure $ Just Show
parse ("list" : _) = pure $ Just List
parse ["bpmn"    ] = do
  putTextLn "missing file path"
  pure Nothing
parse ["smt"] = do
  putTextLn "missing file path"
  pure Nothing
parse ["load"] = do
  putTextLn "missing file path"
  pure Nothing
parse ("bpmn" : path : _) = pure $ Just (Bpmn path)
parse ("smt"  : path : _) = pure $ Just (Smt path)
parse ("load" : path : _) = pure $ Just (Load path)
parse _                   = pure Nothing
