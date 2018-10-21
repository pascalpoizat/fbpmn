module Fbpmn where

import           Data.Monoid                    ( All(..) )
import           Data.List                      ( intercalate )
import           Data.Maybe                     ( isNothing )
import           GHC.Generics
import qualified Data.ByteString.Lazy          as BS
                                                ( ByteString
                                                , writeFile
                                                , readFile
                                                )
import           Data.Aeson                     ( encode
                                                , decode
                                                , FromJSON
                                                , ToJSON
                                                )
import           Data.Map.Strict                ( Map
                                                , (!?)
                                                )
import           System.IO.Error                ( IOError
                                                , catchIOError
                                                , isDoesNotExistError
                                                )

{-|
Generate the JSON representation for a BPMN Graph.
-}
genJSON :: BpmnGraph -> BS.ByteString
genJSON = encode

{-|
Read a BPMN Graph from a JSON file.
-}
readFromJSON :: FilePath -> IO (Maybe BpmnGraph)
readFromJSON p = (decode <$> BS.readFile p) `catchIOError` handler
 where

  handler :: IOError -> IO (Maybe BpmnGraph)
  handler e
    | isDoesNotExistError e = do
      putStrLn "file not found"
      pure Nothing
    | otherwise = do
      putStrLn "unknown error"
      pure Nothing

{-|
Write a BPMN Graph to a JSON file.
-}
writeToJSON :: FilePath -> BpmnGraph -> IO ()
writeToJSON p = BS.writeFile p . encode

{-|
Write a BPMN Graph to an SMT file.
-}
writeToSMT :: FilePath -> BpmnGraph -> IO ()
writeToSMT p = writeFile p . encodeBpmnGraphToSmt

{-|
Write a BPMN Graph to a TLA+ file.
-}
writeToTLA :: FilePath -> BpmnGraph -> IO ()
writeToTLA p = writeFile p . encodeBpmnGraphToTla

{-|
Transform a BPMN Graph to an SMT description.

The solution is to use a model to text transformation.
TODO: In terms of typing, it would be better to use a model to model transformation (first).
-}
encodeBpmnGraphToSmt :: BpmnGraph -> String
encodeBpmnGraphToSmt g = unlines
  [ "; BPMN Graph encoded using fBPMN\n"
  , encodeBpmnGraphNodesToSmt g
  , "; end of encoding"
  ]

encodeBpmnGraphNodesToSmt :: BpmnGraph -> String
encodeBpmnGraphNodesToSmt g = "; Process node declarations\n"
  <> unlines (nodeToNodeDeclaration g <$> nodes g)
 where
  nodeToNodeDeclaration :: BpmnGraph -> Node -> String
  nodeToNodeDeclaration _ n = "(declare-fun " <> n <> " () (Array Int Int))"

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToTla :: BpmnGraph -> String
encodeBpmnGraphToTla g =
  unlines
    $   [ encodeBpmnGraphHeaderToTla
        , encodeBpmnGraphProcessDeclToTla
        , encodeBpmnGraphContainRelToTla
        , encodeBpmnGraphNodeDeclToTla
        , encodeBpmnGraphFlowDeclToTla
        , encodeBpmnGraphMsgDeclToTla
        , encodeBpmnGraphCatNToTla
        , encodeBpmnGraphCatEToTla
        , encodeBpmnGraphFooterToTla
        ]
    <*> [g]

encodeBpmnGraphHeaderToTla :: BpmnGraph -> String
encodeBpmnGraphHeaderToTla g = unlines
  [ "---------------- MODULE " <> name g <> " ----------------"
  , ""
  , "EXTENDS TLC, PWSTypes"
  , ""
  , "VARIABLES nodemarks, edgemarks, net"
  , ""
  , "var == <<nodemarks, edgemarks, net>>"
  ]

encodeBpmnGraphFooterToTla :: BpmnGraph -> String
encodeBpmnGraphFooterToTla g = unlines
  [ ""
  , "WF == INSTANCE PWSWellFormed"
  , "ASSUME WF!WellFormedness"
  , ""
  , "INSTANCE PWSSemantics"
  , ""
  , "Spec == Init /\\ [][Next]_var /\\ WF_var(Next)"
  , ""
  , "================================================================"
  ]

-- TODO: extend with multiple processes
encodeBpmnGraphProcessDeclToTla :: BpmnGraph -> String
encodeBpmnGraphProcessDeclToTla _ = "TopProcess == { \"" <> "Process" <> "\" }"

encodeBpmnGraphContainRelToTla :: BpmnGraph -> String
encodeBpmnGraphContainRelToTla _ = unlines []

encodeBpmnGraphNodeDeclToTla :: BpmnGraph -> String
encodeBpmnGraphNodeDeclToTla _ = unlines []

encodeBpmnGraphFlowDeclToTla :: BpmnGraph -> String
encodeBpmnGraphFlowDeclToTla g = unlines
  [ encodeBpmnGraphFlowDeclToTla' "NormalSeqFlowEdge" sequenceFlows g
  , encodeBpmnGraphFlowDeclToTla' "MsgFlowEdge"       messageFlows  g
  , "Edge == NormalSeqFlowEdge \\union MsgFlowEdge"
  ]

encodeBpmnGraphFlowDeclToTla' :: String
                              -> (BpmnGraph -> [Edge])
                              -> BpmnGraph
                              -> String
encodeBpmnGraphFlowDeclToTla' kindName flowFilter g =
  kindName <> " == {\n" <> intercalate ",\n" flowDecls <> "\t}\n"
 where
  flowDecls :: [String]
  flowDecls = flowToSeqFlowDeclaration <$> flowFilter g
  flowToSeqFlowDeclaration :: Edge -> String
  flowToSeqFlowDeclaration e =
    case
        do
          sourceNode <- sourceE g !? e
          targetNode <- targetE g !? e
          pure (sourceNode, targetNode)
      of
        Nothing      -> ""
        Just (n, n') -> "\t<<\"" <> n <> "\", \"" <> n' <> "\">>"

encodeBpmnGraphMsgDeclToTla :: BpmnGraph -> String
encodeBpmnGraphMsgDeclToTla _ = unlines []

encodeBpmnGraphCatNToTla :: BpmnGraph -> String
encodeBpmnGraphCatNToTla g = "CatN == "
  <> intercalate "\n@@ " (nodeToNodeCatDecl <$> nodes g)
 where
  nodeToNodeCatDecl :: Node -> String
  nodeToNodeCatDecl n = case catN g !? n of
    Nothing -> ""
    Just c  -> "\"" <> n <> "\"" <> " :> " <> toTLA c

encodeBpmnGraphCatEToTla :: BpmnGraph -> String
encodeBpmnGraphCatEToTla _ = unlines
  [ "CatE == [ e \\in Edge |->"
  , "  IF e \\in NormalSeqFlowEdge THEN NormalSeqFlow"
  , "  ELSE MsgFlow"
  ]

toTLA :: NodeType -> String
toTLA AbstractTask = "AbstractTask"
toTLA SendTask = "SendTask"
toTLA ReceiveTask = "ReceiveTask"
toTLA SubProcess = "SubProcess"
toTLA XorGateway = "ExclusiveOr"
toTLA OrGateway = "InclusiveOr"
toTLA AndGateway = "Parallel"
toTLA NoneStartEvent = "StartEvent"
toTLA NoneEndEvent = "EndEvent"

--
-- Node types
--
data NodeType = AbstractTask
              | SendTask
              | ReceiveTask
              | SubProcess
              | XorGateway
              | OrGateway
              | AndGateway
              | NoneStartEvent
              | NoneEndEvent
  deriving (Eq, Show, Generic)
instance ToJSON NodeType
instance FromJSON NodeType

isTask :: NodeType -> Bool
isTask n = n `elem` [AbstractTask, SendTask, ReceiveTask]

isTaskN :: BpmnGraph -> Node -> Maybe Bool
isTaskN g = isInGraph g catN isTask

isInGraph :: (Ord a)
          => BpmnGraph
          -> (BpmnGraph -> Map a b)
          -> (b -> Bool)
          -> a
          -> Maybe Bool
isInGraph g f p x = p <$> f g !? x

--
-- Edge types
--
data EdgeType = NormalSequenceFlow
              | ConditionalSequenceFlow
              | DefaultSequenceFlow
              | MessageFlow
  deriving (Eq, Show, Generic)
instance ToJSON EdgeType
instance FromJSON EdgeType
--
-- Messages
--
type Message = String

--
-- Processes
--
type Process = Int

--
-- XML Ids
--
type Id = String

--
-- Names
--
type Name = String

--
-- Nodes
--
type Node = Id

--
-- Edges
--
type Edge = Id

--
-- BPMN Graph
--
data BpmnGraph = BpmnGraph { name :: String
                           , nodes :: [Node]
                           , edges :: [Edge]
                           , catN :: Map Node NodeType
                           , catE :: Map Edge EdgeType
                           , sourceE :: Map Edge Node
                           , targetE :: Map Edge Node
                           , nameN :: Map Node Name
}
  deriving (Eq, Show, Generic)
instance ToJSON BpmnGraph
instance FromJSON BpmnGraph

mkGraph :: String
        -> [Node]
        -> [Edge]
        -> Map Node NodeType
        -> Map Node EdgeType
        -> Map Edge Node
        -> Map Edge Node
        -> Map Node Name
        -> BpmnGraph
mkGraph n ns es catN catE sourceE targetE nameN =
  let graph = BpmnGraph n ns es catN catE sourceE targetE nameN in graph

--
-- nodesT for one type
--
nodesT :: BpmnGraph -> NodeType -> [Node]
nodesT g t = filter' (nodes g) (catN g) (== Just t)

--
-- nodesT for several types
--
nodesTs :: BpmnGraph -> [NodeType] -> [Node]
nodesTs g ts = concat $ nodesT g <$> ts

--
-- nodesE for one type
--
edgesT :: BpmnGraph -> EdgeType -> [Edge]
edgesT g t = filter' (edges g) (catE g) (== Just t)

--
-- nodesE for several types
--
edgesTs :: BpmnGraph -> [EdgeType] -> [Edge]
edgesTs g ts = concat $ edgesT g <$> ts

--
-- sequence flows
--
sequenceFlows :: BpmnGraph -> [Edge]
sequenceFlows g =
  edgesTs g [NormalSequenceFlow, ConditionalSequenceFlow, DefaultSequenceFlow]

--
-- message flows
--
messageFlows :: BpmnGraph -> [Edge]
messageFlows g = edgesT g MessageFlow

--
-- helper
--
filter' :: (Ord a) => [a] -> (Map a b) -> (Maybe b -> Bool) -> [a]
filter' xs f p = filter p' xs where p' x = p $ f !? x

--
-- in
--
inN :: BpmnGraph -> Node -> [Edge]
inN g n = [ e | e <- edges g, target !? e == Just n ] where target = targetE g

--
-- out
--
outN :: BpmnGraph -> Node -> [Edge]
outN g n = [ e | e <- edges g, source !? e == Just n ]
  where source = sourceE g

--
-- inT
--
inT :: BpmnGraph -> Node -> EdgeType -> [Edge]
inT g n t = [ e1 | e1 <- edgesT g t, e2 <- inN g n, e1 == e2 ]

--
-- outT
--
outT :: BpmnGraph -> Node -> EdgeType -> [Edge]
outT g n t = [ e1 | e1 <- edgesT g t, e2 <- outN g n, e1 == e2 ]

--
-- checks
--
isValidGraph :: BpmnGraph -> Bool
isValidGraph g =
  and
    $   [ allNodesHave catN -- \forall n \in N . n \in dom(catN)
        , allEdgesHave catE -- \forall e \in E . e \in dom(catE) 
        , allEdgesHave sourceE -- \forall e \in E . e \in dom(sourceE)
        , allEdgesHave targetE -- \forall e \in E . e \in dom(targetE)
        , allValidMessageFlow -- \forall m in E^{MessageFlow} . sourceE(e) \in E^{SendTask} /\ target(e) \in E^{ReceiveTask}
        ]
    <*> [g]

isValidMessageFlow :: BpmnGraph -> Edge -> Bool
isValidMessageFlow g mf =
  case
      do
        source <- sourceE g !? mf
        target <- targetE g !? mf
        cats   <- catN g !? source
        catt   <- catN g !? target
        pure (cats, catt)
    of
      Nothing       -> False
      Just (cs, ct) -> cs == SendTask && ct == ReceiveTask

allValidMessageFlow :: BpmnGraph -> Bool
allValidMessageFlow g =
  getAll $ foldMap (All . isValidMessageFlow g) $ messageFlows g

allNodesHave :: (BpmnGraph -> Map Node b) -> BpmnGraph -> Bool
allNodesHave = allDefF nodes

allEdgesHave :: (BpmnGraph -> Map Edge b) -> BpmnGraph -> Bool
allEdgesHave = allDefF edges

allDefF :: (Ord a, Foldable t, Functor t)
        => (BpmnGraph -> t a)
        -> (BpmnGraph -> Map a b)
        -> BpmnGraph
        -> Bool
allDefF h f g = allDef (h g) f g

allDef :: (Ord a, Foldable t, Functor t)
       => t a
       -> (BpmnGraph -> Map a b)
       -> BpmnGraph
       -> Bool
allDef xs f g = not $ any isNothing $ (m !?) <$> xs where m = f g
