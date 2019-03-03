import           Options.Applicative
import           Fbpmn.Model
import           Fbpmn.IO.Bpmn
import           Fbpmn.IO.Json
import           Fbpmn.IO.Smt
import           Fbpmn.IO.Tla
import           Examples                       ( models )
import           Data.Map.Strict                ( keys
                                                , (!?)
                                                )

data RCommand = RQuit        -- quit REPL
             | RHelp        -- list commands
             | RList        -- list internal examples
             | RShow        -- show current graph
             | RImport Text -- load current graph from internal examples
             | RLoad Text   -- load current graph from JSON and verify file
             | RBpmn Text   -- load current graph as BPMN
             | RJson Text   -- save current graph as JSON
             | RSmt Text    -- save current graph as SMT
             | RTla Text    -- save current graph as TLA+

fversion :: Text
fversion = "0.1"

fname :: Text
fname = "fbpmn"

toolversion :: Text
toolversion = fname <> " " <> fversion

data Suffix = JsonSuffix | BpmnSuffix | TlaSuffix
  deriving (Eq)

jsonSuffix :: Text
jsonSuffix = ".json"

bpmnSuffix :: Text
bpmnSuffix = ".bpmn"

tlaSuffix :: Text
tlaSuffix = ".tla"

newtype Options = Options
  { optCommand :: Command
  }

data Command
  = CVersion
  | CRepl
  | CJson2Tla { optPath :: Text }
  | CBpmn2Json { optPath :: Text }
  | CBpmn2Tla { optPath :: Text }

parserOptions :: Parser Options
parserOptions = Options <$> subparser
  (  command "version" (info (pure CVersion) (progDesc "prints the version"))
  <> command "repl"    (info (pure CRepl) (progDesc "launches the REPL"))
  <> command
       "json2tla"
       (info parserJson2Tla
             (progDesc "transforms a collaboration from JSON to TLA+")
       )
  <> command
       "bpmn2json"
       (info parserBpmn2Json
             (progDesc "transforms a collaboration from BPMN to BPMN")
       )
  <> command
       "bpmn2tla"
       (info parserBpmn2Tla
             (progDesc "transforms a collaboration from BPMN to TLA+")
       )
  )

parserJson2Tla :: Parser Command
parserJson2Tla = CJson2Tla <$> argument
  str
  (  metavar "PATH"
  <> help "path to the input model in JSON format (without .json suffix)"
  )

parserBpmn2Json :: Parser Command
parserBpmn2Json = CBpmn2Json <$> argument
  str
  (  metavar "PATH"
  <> help "path to the input model in BPMN format (without .bpmn suffix)"
  )

parserBpmn2Tla :: Parser Command
parserBpmn2Tla = CBpmn2Tla <$> argument
  str
  (  metavar "PATH"
  <> help "path to the input model in BPMN format (without .bpmn suffix)"
  )

run :: Options -> IO ()
run (Options CVersion      ) = putStrLn toolversion
run (Options CRepl         ) = repl ("()", Nothing)
run (Options (CJson2Tla  p)) = json2tla p
run (Options (CBpmn2Json p)) = bpmn2json p
run (Options (CBpmn2Tla  p)) = bpmn2tla p

transform :: Text
          -> Text
          -> (String -> IO (Maybe BpmnGraph))
          -> (String -> BpmnGraph -> IO ())
          -> Text
          -> IO ()
transform sourceSuffix targetSuffix mreader mwriter path = do
  loadres <- mreader (toString $ path <> sourceSuffix)
  case loadres of
    Nothing    -> putTextLn "wrong file"
    Just graph -> if isValidGraph graph
      then do
        mwriter (toString $ path <> targetSuffix) graph
        putTextLn "transformation done"
      else putTextLn "graph is incorrect"

json2tla :: Text -> IO ()
json2tla = transform jsonSuffix tlaSuffix readFromJSON writeToTLA

bpmn2json :: Text -> IO ()
bpmn2json = transform bpmnSuffix jsonSuffix readFromBPMN writeToJSON

bpmn2tla :: Text -> IO ()
bpmn2tla = transform bpmnSuffix tlaSuffix readFromBPMN writeToTLA

main :: IO ()
main = run =<< execParser opts
 where
  opts = info
    (parserOptions <**> helper)
    (fullDesc <> progDesc "formal transformations for BPMN models" <> header
      (toString toolversion)
    )

{-|
The REPL.
TODO: use State monad.
-}
repl :: (Text, Maybe BpmnGraph) -> IO ()
repl (p, g) = do
  putStrLn $ p <> " > "
  rawinput <- getLine
  rcommand <- rparse (words rawinput)
  case rcommand of
    Nothing -> do
      putTextLn "unknown command"
      repl (p, g)
    Just RHelp -> do
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
    Just RQuit -> putTextLn "goodbye"
    Just RShow -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        print g'
        repl (p, g)
    Just RList -> do
      print $ keys models
      repl (p, g)
    Just (RImport name) -> case models !? name of
      Nothing -> do
        putTextLn "unknown example"
        repl (p, g)
      Just g' -> do
        putTextLn "example loaded"
        repl (name, Just g')
    Just (RJson path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToJSON (toString path) g'
        repl (p, g)
    Just (RBpmn path) -> do
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
    Just (RSmt path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToSMT (toString path) g'
        repl (p, g)
    Just (RTla path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToTLA (toString path) g'
        repl (p, g)
    Just (RLoad path) -> do
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

rparse :: [Text] -> IO (Maybe RCommand)
rparse ("quit" : _) = pure $ Just RQuit
rparse ("help" : _) = pure $ Just RHelp
rparse ("show" : _) = pure $ Just RShow
rparse ("list" : _) = pure $ Just RList
rparse ["import"  ] = do
  putTextLn "missing example name"
  pure Nothing
rparse ["json"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["bpmn"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["smt"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["tla"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["load"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ("import" : name : _) = pure $ Just (RImport name)
rparse ("json"   : path : _) = pure $ Just (RJson path)
rparse ("bpmn"   : path : _) = pure $ Just (RBpmn path)
rparse ("smt"    : path : _) = pure $ Just (RSmt path)
rparse ("tla"    : path : _) = pure $ Just (RTla path)
rparse ("load"   : path : _) = pure $ Just (RLoad path)
rparse _                     = pure Nothing
