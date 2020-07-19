
import           Colourista                     ( successMessage
                                                , infoMessage
                                                , warningMessage
                                                , errorMessage
                                                )
import           Options.Applicative
import           Fbpmn.BpmnGraph.Model
import           Fbpmn.BpmnGraph.IO.Bpmn
import qualified Fbpmn.BpmnGraph.IO.Dot        as BGD
import qualified Fbpmn.BpmnGraph.IO.Json       as BG
import           Fbpmn.Analysis.Alloy.IO.Alloy
import           Fbpmn.Analysis.Tla.Model
import           Fbpmn.Analysis.Tla.IO.Tla
import qualified Fbpmn.Analysis.Tla.IO.Json    as TL
import qualified Fbpmn.Analysis.Tla.IO.Dot     as TLD
import           Fbpmn.Analysis.Tla.IO.Html
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
             | RAlloy Text  -- save current graph as Alloy
            -- to be deprecated: 
             -- | RList        -- list internal examples
             -- | RShow        -- show current graph
             -- | RImport Text -- load current graph from internal examples
             -- | RSmt Text    -- save current graph as SMT

fversion :: Text
fversion = "0.3.4"

toolversion :: Text
toolversion = fversion

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

alloySuffix :: Text
alloySuffix = ".als"

htmlSuffix :: Text
htmlSuffix = ".html"

newtype Options = Options Command

data Command
  = CVersion
  | CRepl
  -- transformations from JSON
  | CJson2Dot Text Text
  | CJson2Tla Text Text
  | CJson2Alloy Text Text
  -- transformations from BPMN
  | CBpmn2Json Text Text
  | CBpmn2Tla Text Text
  | CBpmn2Alloy Text Text
  -- transformations from TLA+ logs
  | CLog2Json Text Text
  | CLog2Dot Text Text
  | CLog2Html Text Text

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
       "json2alloy"
       (info parserJson2Alloy
             (progDesc "transforms a collaboration from JSON to Alloy")
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
       "bpmn2alloy"
       (info parserBpmn2Alloy
             (progDesc "transforms a collaboration from BPMN to Alloy")
       )
  <> command
       "log2json"
       (info parserLog2Json
             (progDesc "transforms a TLA+ log from LOG to JSON")
       )
  <> command
       "log2dot"
       (info parserLog2Dot (progDesc "transforms a TLA+ log from LOG to DOT"))
  <> command
       "log2html"
       (info parserLog2Html
             (progDesc "transforms a TLA+ log from LOG to HTML")
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

parserJson2Alloy :: Parser Command
parserJson2Alloy =
  CJson2Alloy
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in JSON format (without .json suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in Alloy format (without .als suffix)"
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

parserBpmn2Alloy :: Parser Command
parserBpmn2Alloy =
  CBpmn2Alloy
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in BPMN format (without .bpmn suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in Alloy format (without .als suffix)"
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

parserLog2Dot :: Parser Command
parserLog2Dot =
  CLog2Dot
    <$> argument
          str
          (  metavar "INPUT-PATH"
          <> help
               "path to the input TLA+ log in textual format (without .log suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in DOT format (without .dot suffix)"
          )

parserLog2Html :: Parser Command
parserLog2Html =
  CLog2Html
    <$> argument
          str
          (  metavar "INPUT-PATH"
          <> help
               "path to the input TLA+ log in textual format (without .log suffix)"
          )
    <*> argument
          str
          (metavar "OUTPUT-PATH" <> help
            "path to the output file in HTML format (without .html suffix)"
          )

-- no validation needed from BPMN since we build the graph ourselves
run :: Options -> IO ()
run (Options CVersion              ) = putStrLn . toString $ toolversion
run (Options CRepl                 ) = repl ("()", Nothing)
run (Options (CJson2Dot   pin pout)) = json2dot True pin pout Nothing
run (Options (CJson2Tla   pin pout)) = json2tla True pin pout Nothing
run (Options (CJson2Alloy pin pout)) = json2alloy True pin pout Nothing
run (Options (CBpmn2Json  pin pout)) = bpmn2json False pin pout Nothing
run (Options (CBpmn2Tla   pin pout)) = bpmn2tla False pin pout Nothing
run (Options (CBpmn2Alloy pin pout)) = bpmn2alloy False pin pout Nothing
run (Options (CLog2Json   pin pout)) = log2json False pin pout Nothing
run (Options (CLog2Dot    pin pout)) = log2dot False pin pout Nothing
run (Options (CLog2Html   pin pout)) = log2html False pin pout Nothing

transform2 :: Text                                       -- input file suffix
           -> Text                                       -- output file suffix
           -> (FilePath -> Maybe String -> IO (Maybe a)) -- reader (from input file to model)
           -> (FilePath -> Maybe String -> a -> IO ())   -- writer (from model to output file)
           -> (a -> Bool)                                -- model validator
           -> (a -> a)                                   -- model filtering
           -> Bool                                       -- should validation be done?
           -> Text                                       -- input file (without suffix)
           -> Text                                       -- output file (without suffix)
           -> Maybe String                               -- additional information (can be used to related to a source model)
           -> IO ()
transform2 sourceSuffix targetSuffix mreader mwriter modelValidator modelFilter withValidation inputPath outputPath minfo
  = do
    loadres <- mreader (toString $ inputPath <> sourceSuffix) minfo
    case loadres of
      Nothing    -> errorMessage "wrong file"
      Just model -> if not withValidation || modelValidator model
        then do
          mwriter (toString $ outputPath <> targetSuffix)
                  minfo
                  (modelFilter model)
          successMessage "transformation done"
        else errorMessage "model is incorrect"

json2dot :: Bool -> Text -> Text -> Maybe String -> IO ()
json2dot =
  transform2 jsonSuffix dotSuffix BG.readFromJSON BGD.writeToDOT isValidGraph id

json2tla :: Bool -> Text -> Text -> Maybe String -> IO ()
json2tla =
  transform2 jsonSuffix tlaSuffix BG.readFromJSON writeToTLA isValidGraph id

json2alloy :: Bool -> Text -> Text -> Maybe String -> IO ()
json2alloy =
  transform2 jsonSuffix alloySuffix BG.readFromJSON writeToAlloy isValidGraph id

bpmn2json :: Bool -> Text -> Text -> Maybe String -> IO ()
bpmn2json =
  transform2 bpmnSuffix jsonSuffix readFromBPMN BG.writeToJSON isValidGraph id

bpmn2tla :: Bool -> Text -> Text -> Maybe String -> IO ()
bpmn2tla =
  transform2 bpmnSuffix tlaSuffix readFromBPMN writeToTLA isValidGraph id

bpmn2alloy :: Bool -> Text -> Text -> Maybe String -> IO ()
bpmn2alloy =
  transform2 bpmnSuffix alloySuffix readFromBPMN writeToAlloy isValidGraph id

log2json :: Bool -> Text -> Text -> Maybe String -> IO ()
log2json = transform2 logSuffix
                      jsonSuffix
                      readFromLOG
                      TL.writeToJSON
                      isValidLog
                      filterLog

log2dot :: Bool -> Text -> Text -> Maybe String -> IO ()
log2dot =
  transform2 logSuffix dotSuffix readFromLOG TLD.writeToDOT isValidLog filterLog

log2html :: Bool -> Text -> Text -> Maybe String -> IO ()
log2html =
  transform2 logSuffix htmlSuffix readFromLOG writeToHTML isValidLog filterLog

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
  infoMessage $ p <> " > "
  rawinput <- getLine
  rcommand <- rparse (words rawinput)
  case rcommand of
    Nothing -> do
      errorMessage "unknown command"
      repl (p, g)
    Just RHelp -> do
      infoMessage $ unlines
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
    Just RQuit       -> infoMessage "goodbye"
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
        errorMessage "no graph loaded"
        repl (p, g)
      Just g' -> do
        BGD.writeToDOT (toString path) Nothing g'
        repl (p, g)
    Just (RJson path) -> case g of
      Nothing -> do
        errorMessage "no graph loaded"
        repl (p, g)
      Just g' -> do
        BG.writeToJSON (toString path) Nothing g'
        repl (p, g)
    Just (RBpmn path) -> do
      loadres <- readFromBPMN (toString path) Nothing
      case loadres of
        Nothing -> do
          errorMessage "wrong file"
          repl (p, g)
        Just graph -> if isValidGraph graph
          then do
            infoMessage "graph is correct"
            repl ("(" <> path <> ")", Just graph)
          else do
            errorMessage "graph is incorrect"
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
        errorMessage "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToTLA (toString path) Nothing g'
        repl (p, g)
    Just (RAlloy path) -> case g of
      Nothing -> do
        errorMessage "no graph loaded"
        repl (p, g)
      Just g' -> do
        writeToAlloy (toString path) Nothing g'
        repl (p, g)
    Just (RLoad path) -> do
      loadres <- BG.readFromJSON (toString path) Nothing
      case loadres of
        Nothing -> do
          errorMessage "wrong file"
          repl (p, g)
        Just graph -> if isValidGraph graph
          then do
            infoMessage "graph is correct"
            repl ("(" <> path <> ")", Just graph)
          else do
            errorMessage "graph is incorrect"
            repl (p, g)

rparse :: [Text] -> IO (Maybe RCommand)
rparse ("quit" : _) = pure $ Just RQuit
rparse ("help" : _) = pure $ Just RHelp
-- rparse ("show" : _) = pure $ Just RShow
-- rparse ("list" : _) = pure $ Just RList
-- rparse ["import"  ] = do
--   putTextLn "missing example name"
--   pure Nothing
rparse ["dot"] = do
  errorMessage "missing file path"
  pure Nothing
rparse ["json"] = do
  errorMessage "missing file path"
  pure Nothing
rparse ["bpmn"] = do
  errorMessage "missing file path"
  pure Nothing
-- rparse ["smt"] = do
--   putTextLn "missing file path"
--   pure Nothing
rparse ["tla"] = do
  errorMessage "missing file path"
  pure Nothing
rparse ["load"] = do
  errorMessage "missing file path"
  pure Nothing
-- rparse ("import" : name : _) = pure $ Just (RImport name)
rparse ("dot"  : path : _) = pure $ Just (RDot path)
rparse ("json" : path : _) = pure $ Just (RJson path)
rparse ("bpmn" : path : _) = pure $ Just (RBpmn path)
-- rparse ("smt"    : path : _) = pure $ Just (RSmt path)
rparse ("tla"  : path : _) = pure $ Just (RTla path)
rparse ("load" : path : _) = pure $ Just (RLoad path)
rparse _                   = pure Nothing
