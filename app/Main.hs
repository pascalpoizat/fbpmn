import           Fbpmn
import           Examples                       ( g1 )
import           Data.Map.Strict                ( keys )

data Command = Quit       -- quit REPL
             | List       -- list internal examples
             | Load Text  -- load and verify file
             -- | Save Text  -- save graph

examples :: Map Text BpmnGraph
examples = fromList [("g1", g1)]

main :: IO ()
main = repl

repl :: IO ()
repl = do
  putTextLn "enter command > "
  rawinput <- getLine
  command  <- parse (words rawinput)
  case command of
    Nothing -> do
      putTextLn "unknown command"
      repl
    Just Quit        -> putTextLn "goodbye"
    Just List        -> do
                          print $ keys examples
                          repl
    Just (Load path) -> do
      loadres <- readFromJSON (toString path)
      case loadres of
        Nothing -> do
          putTextLn "wrong file"
          repl
        Just graph -> if isValidGraph graph
          then do
            putTextLn "graph is correct"
            repl
          else do
            putTextLn "graph is incorrect"
            repl

parse :: [Text] -> IO (Maybe Command)
parse ("quit" : _) = pure $ Just Quit
parse ("list" : _) = pure $ Just List
parse ["load"    ] = do
  putTextLn "missing file path"
  pure Nothing
parse ("load" : path : _) = pure $ Just (Load path)
parse _                   = pure Nothing
