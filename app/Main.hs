
import           Colourista                     ( successMessage
                                                , errorMessage
                                                )
import           Options.Applicative
import           Fbpmn.BpmnGraph.Model
import           Fbpmn.BpmnGraph.SpaceModel
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
import Fbpmn.Helper (TEither)
-- import           Fbpmn.IO.Smt
-- import           Examples                       ( models )
-- import           Data.Map.Strict                ( keys
--                                                 , (!?)
--                                                 )

fversion :: Text
fversion = "0.3.5"

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
  -- transformations from JSON (regular BPMN models)
  | CJson2Dot Text Text
  | CJson2Tla Text Text
  | CJson2Alloy Text Text
  -- transformations from regular BPMN models
  | CBpmn2Json Text Text
  | CBpmn2Tla Text Text
  | CBpmn2Alloy Text Text
  -- transformations from space BPMN models
  | CSBpmn2Tla Text Text
  -- transformations from TLA+ logs
  | CLog2Json Text Text
  | CLog2Dot Text Text
  | CLog2Html Text Text

parserOptions :: Parser Options
parserOptions = Options <$> subparser
  (  command "version" (info (pure CVersion) (progDesc "prints the version"))
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
       "sbpmn2tla"
       (info parserSBpmn2Tla
             (progDesc "transforms a collaboration from space BPMN to TLA+")
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

parserSBpmn2Tla :: Parser Command
parserSBpmn2Tla =
  CSBpmn2Tla
    <$> argument
          str
          (metavar "INPUT-PATH" <> help
            "path to the input model in space BPMN format (without .bpmn suffix)"
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
run (Options (CJson2Dot   pin pout)) = json2dot True pin pout
run (Options (CJson2Tla   pin pout)) = json2tla True pin pout
run (Options (CJson2Alloy pin pout)) = json2alloy True pin pout
run (Options (CBpmn2Json  pin pout)) = bpmn2json False pin pout
run (Options (CBpmn2Tla   pin pout)) = bpmn2tla False pin pout
run (Options (CBpmn2Alloy pin pout)) = bpmn2alloy False pin pout
run (Options (CSBpmn2Tla  pin pout)) = sbpmn2tla False pin pout
run (Options (CLog2Json   pin pout)) = log2json False pin pout
run (Options (CLog2Dot    pin pout)) = log2dot False pin pout
run (Options (CLog2Html   pin pout)) = log2html False pin pout

transform2 :: Text                             -- input file suffix
           -> Text                             -- output file suffix
           -> (FilePath -> IO (TEither a)) -- reader (from input file to model)
           -> (FilePath -> a -> IO ())         -- writer (from model to output file)
           -> (a -> Bool)                      -- model validator
           -> (a -> a)                         -- model filtering
           -> Bool                             -- should validation be done?
           -> Text                             -- input file (without suffix)
           -> Text                             -- output file (without suffix)
           -> IO ()
transform2 sourceSuffix targetSuffix mreader mwriter modelValidator modelFilter withValidation inputPath outputPath
  = do
    loadres <- mreader (toString $ inputPath <> sourceSuffix)
    case loadres of
      Left err   -> errorMessage err
      Right model -> if not withValidation || modelValidator model
        then do
          mwriter (toString $ outputPath <> targetSuffix)
                  (modelFilter model)
          successMessage "transformation done"
        else errorMessage "model is incorrect"

json2dot :: Bool -> Text -> Text -> IO ()
json2dot =
  transform2 jsonSuffix dotSuffix BG.readFromJSON BGD.writeToDOT isValidGraph id

json2tla :: Bool -> Text -> Text -> IO ()
json2tla =
  transform2 jsonSuffix tlaSuffix BG.readFromJSON writeToTLA isValidGraph id

json2alloy :: Bool -> Text -> Text -> IO ()
json2alloy =
  transform2 jsonSuffix alloySuffix BG.readFromJSON writeToAlloy isValidGraph id

bpmn2json :: Bool -> Text -> Text -> IO ()
bpmn2json =
  transform2 bpmnSuffix jsonSuffix (readFromXML decodeBPMN) BG.writeToJSON isValidGraph id

bpmn2tla :: Bool -> Text -> Text -> IO ()
bpmn2tla =
  transform2 bpmnSuffix tlaSuffix (readFromXML decodeBPMN) writeToTLA isValidGraph id

bpmn2alloy :: Bool -> Text -> Text -> IO ()
bpmn2alloy =
  transform2 bpmnSuffix alloySuffix (readFromXML decodeBPMN) writeToAlloy isValidGraph id

sbpmn2tla :: Bool -> Text -> Text -> IO ()
sbpmn2tla =
  transform2 bpmnSuffix tlaSuffix (readFromXML decodeSBPMN) writeToSTLA isValidSGraph id

log2json :: Bool -> Text -> Text -> IO ()
log2json = transform2 logSuffix
                      jsonSuffix
                      readFromLOG
                      TL.writeToJSON
                      isValidLog
                      filterLog

log2dot :: Bool -> Text -> Text -> IO ()
log2dot =
  transform2 logSuffix dotSuffix readFromLOG TLD.writeToDOT isValidLog filterLog

log2html :: Bool -> Text -> Text -> IO ()
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
