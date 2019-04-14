import           Options.Applicative
import           Fbpmn.BpmnGraph.Model
import           Fbpmn.BpmnGraph.IO.Bpmn
import           Fbpmn.BpmnGraph.IO.Dot
import qualified Fbpmn.BpmnGraph.IO.Json       as BG
import           Fbpmn.Analysis.Tla.Model
import           Fbpmn.Analysis.Tla.IO.Tla
import qualified Fbpmn.Analysis.Tla.IO.Json    as TL
import           Fbpmn.Analysis.Tla.IO.Log
-- import           Fbpmn.IO.Smt
-- import           Examples                       ( models )
-- import           Data.Map.Strict                ( keys
--                                                 , (!?)
--                                                 )

data RCommand = RQuit        -- quit REPL
             | RHelp        -- list commands
             | RLoad Text   -- load current graph from JSON and verify file
             | RBpmn Text   -- load current graph as BPMN
             | RDot Text    -- save current graph as DOT
             | RJson Text   -- save current graph as JSON
             | RTla Text    -- save current graph as TLA+
            -- to be deprecated: 
             -- | RList        -- list internal examples
             -- | RShow        -- show current graph
             -- | RImport Text -- load current graph from internal examples
             -- | RSmt Text    -- save current graph as SMT

fversion :: Text
fversion = "0.2.5"

toolversion :: Text
toolversion = fversion

data Suffix = JsonSuffix | BpmnSuffix | TlaSuffix
  deriving (Eq)

dotSuffix :: Text
dotSuffix = ".dot"

jsonSuffix :: Text
jsonSuffix = ".json"

bpmnSuffix :: Text
bpmnSuffix = ".bpmn"

tlaSuffix :: Text
tlaSuffix = ".tla"

logSuffix :: Text
logSuffix = ".log"

newtype Options = Options Command

data Command
  = CVersion
  | CRepl
  | CJson2Dot Text Text
  | CJson2Tla Text Text
  | CBpmn2Json Text Text
  | CBpmn2Tla Text Text
  | CLog2Json Text Text

parserOptions :: Parser Options
parserOptions = Options <$> subparser
  (  command "version" (info (pure CVersion) (progDesc "prints the version"))
  <> command "repl"    (info (pure CRepl) (progDesc "launches the REPL"))
  <> command
       "json2dot"
       (info parserJson2Dot
             (progDesc "transforms a collaboration from JSON to DOT")
       )
  <> command
       "json2tla"
       (info parserJson2Tla
             (progDesc "transforms a collaboration from JSON to TLA+")
       )
  <> command
       "bpmn2json"
       (info parserBpmn2Json
             (progDesc "transforms a collaboration from BPMN to JSON")
       )
  <> command
       "bpmn2tla"
       (info parserBpmn2Tla
             (progDesc "transforms a collaboration from BPMN to TLA+")
       )
  <> command
       "log2json"
       (info parserLog2Json
             (progDesc "transforms a TLA+ log from LOG to JSON")
       )
  )

parserJson2Dot :: Parser Command
parserJson2Dot =
  CJson2Dot
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in JSON format (without .json suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in DOT format (without .dot suffix)"
          )

parserJson2Tla :: Parser Command
parserJson2Tla =
  CJson2Tla
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in JSON format (without .json suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in TLA+ format (without .tla suffix)"
          )

parserBpmn2Json :: Parser Command
parserBpmn2Json =
  CBpmn2Json
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in BPMN format (without .bpmn suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in JSON format (without .json suffix)"
          )

parserBpmn2Tla :: Parser Command
parserBpmn2Tla =
  CBpmn2Tla
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in BPMN format (without .bpmn suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in TLA+ format (without .tla suffix)"
          )

parserLog2Json :: Parser Command
parserLog2Json =
  CLog2Json
    <$> argument
          str
          (  metavar "INPUT-PATH"
          <> help
               "path to the input TLA+ log in textual format (without .log suffix)"
          )
    <*> argument
          str
          (  metavar "OUTPUT-PATH"
          <> help
               "path to the output TLA+ log in JSON format (without .json suffix)"
          )

-- no validation needed from BPMN since we build the graph ourselves
run :: Options -> IO ()
run (Options CVersion             ) = putStrLn toolversion
run (Options CRepl                ) = repl ("()", Nothing)
run (Options (CJson2Dot  pin pout)) = json2dot True pin pout
run (Options (CJson2Tla  pin pout)) = json2tla True pin pout
run (Options (CBpmn2Json pin pout)) = bpmn2json False pin pout
run (Options (CBpmn2Tla  pin pout)) = bpmn2tla False pin pout
run (Options (CLog2Json  pin pout)) = log2json False pin pout

transform2 :: Text                      -- input file suffix
           -> Text                      -- output file suffix
           -> (String -> IO (Maybe a))  -- reader (from input file from model)
           -> (String -> a -> IO ())    -- writer (from model to output file)
           -> (a -> Bool)               -- model validator
           -> Bool                      -- should validation be done?
           -> Text                      -- input file (without suffix)
           -> Text                      -- output file (without suffix)
           -> IO ()
transform2 sourceSuffix targetSuffix mreader mwriter validator withValidation inputPath outputPath
  = do
    loadres <- mreader (toString $ inputPath <> sourceSuffix)
    case loadres of
      Nothing    -> putLTextLn "wrong file"
      Just model -> if not withValidation || validator model
        then do
          mwriter (toString $ outputPath <> targetSuffix) model
          putTextLn "transformation done"
        else putTextLn "model is incorrect"

json2dot :: Bool -> Text -> Text -> IO ()
json2dot =
  transform2 jsonSuffix dotSuffix BG.readFromJSON writeToDOT isValidGraph

json2tla :: Bool -> Text -> Text -> IO ()
json2tla =
  transform2 jsonSuffix tlaSuffix BG.readFromJSON writeToTLA isValidGraph

bpmn2json :: Bool -> Text -> Text -> IO ()
bpmn2json =
  transform2 bpmnSuffix jsonSuffix readFromBPMN BG.writeToJSON isValidGraph

bpmn2tla :: Bool -> Text -> Text -> IO ()
bpmn2tla = transform2 bpmnSuffix tlaSuffix readFromBPMN writeToTLA isValidGraph

log2json :: Bool -> Text -> Text -> IO ()
log2json =
  transform2 logSuffix jsonSuffix readFromLOG TL.writeToJSON isValidLog

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
        -- , "list (list internal examples)"
        -- , "show (show current graph)"
        -- , "import (load current graph from internal examples)"
        , "load (load current graph from JSON and verify file)"
        , "bpmn (load current graph from BPMN)"
        , "json (save current graph to JSON)"
        , "dot (save current graph to DOT)"
        -- , "smt (save current graph as SMT)"
        , "tla  (save current graph to TLA+)"
        ]
      repl (p, g)
    Just RQuit       -> putTextLn "goodbye"
    -- Just RShow -> case g of
    --   Nothing -> do
    --     putTextLn "no graph loaded"
    --     repl (p, g)
    --   Just g' -> do
    --     print g'
    --     repl (p, g)
    -- Just RList -> do
    --   print $ keys models
    --   repl (p, g)
    -- Just (RImport name) -> case models !? name of
    --   Nothing -> do
    --     putTextLn "unknown example"
    --     repl (p, g)
    --   Just g' -> do
    --     putTextLn "example loaded"
    --     repl (name, Just g')
    Just (RDot path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToDOT (toString path) g'
        repl (p, g)
    Just (RJson path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        BG.writeToJSON (toString path) g'
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
    -- Just (RSmt path) -> case g of
    --   Nothing -> do
    --     putTextLn "no graph loaded"
    --     repl (p, g)
    --   Just g' -> do
    --     writeToSMT (toString path) g'
    --     repl (p, g)
    Just (RTla path) -> case g of
      Nothing -> do
        putTextLn "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToTLA (toString path) g'
        repl (p, g)
    Just (RLoad path) -> do
      loadres <- BG.readFromJSON (toString path)
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
-- rparse ("show" : _) = pure $ Just RShow
-- rparse ("list" : _) = pure $ Just RList
-- rparse ["import"  ] = do
--   putTextLn "missing example name"
--   pure Nothing
rparse ["dot"     ] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["json"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["bpmn"] = do
  putTextLn "missing file path"
  pure Nothing
-- rparse ["smt"] = do
--   putTextLn "missing file path"
--   pure Nothing
rparse ["tla"] = do
  putTextLn "missing file path"
  pure Nothing
rparse ["load"] = do
  putTextLn "missing file path"
  pure Nothing
-- rparse ("import" : name : _) = pure $ Just (RImport name)
rparse ("dot"  : path : _) = pure $ Just (RDot path)
rparse ("json" : path : _) = pure $ Just (RJson path)
rparse ("bpmn" : path : _) = pure $ Just (RBpmn path)
-- rparse ("smt"    : path : _) = pure $ Just (RSmt path)
rparse ("tla"  : path : _) = pure $ Just (RTla path)
rparse ("load" : path : _) = pure $ Just (RLoad path)
rparse _                   = pure Nothing
