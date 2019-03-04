module Fbpmn.Model where

import           Data.Aeson                     ( FromJSON
                                                , ToJSON
                                                )
-- import           Data.Monoid                    ( All(..) )
-- import           Data.Maybe                     ( isNothing )
-- import           GHC.Generics
import           Data.Map.Strict                ( Map
                                                , (!?)
                                                , keys
                                                )

--
-- Node types
--
data NodeType = AbstractTask
              | SendTask
              | ReceiveTask
              | ThrowMessageIntermediateEvent
              | CatchMessageIntermediateEvent
              | SubProcess
              | XorGateway
              | OrGateway
              | AndGateway
              | EventBasedGateway
              | NoneStartEvent
              | MessageStartEvent
              | NoneEndEvent
              | TerminateEndEvent
              | MessageEndEvent
              | Process -- for top-level processes
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
data BpmnGraph = BpmnGraph { name     :: Text -- name of the model
                           , nodes    :: [Node] -- nodes (including sub-processes and top-level processes)
                           , edges    :: [Edge] -- edges
                           , catN     :: Map Node NodeType -- gives the category of a node
                           , catE     :: Map Edge EdgeType -- gives the category of an edge
                           , sourceE  :: Map Edge Node -- gives the source of an edge
                           , targetE  :: Map Edge Node -- gives the target of an edge
                           , nameN    :: Map Node Name -- gives the name of a node
                           , containN :: Map Node [Node] -- gives the nodes directly contained in a node n (n must be a subprocess or a process)
                           , containE :: Map Node [Edge] -- gives the edges (not the messageFlows) directly contained in a node n (n must be a subprocess of a process)
                           , messages :: [Message] -- gives all messages types
                           , messageN :: Map Node [Message] -- message types associated to nodes (for now, only for SendTasks and ReceiveTasks)
}
  deriving (Eq, Show, Generic)
instance ToJSON BpmnGraph
instance FromJSON BpmnGraph

mkGraph :: Text
        -> [Node]
        -> [Edge]
        -> Map Node NodeType
        -> Map Node EdgeType
        -> Map Edge Node
        -> Map Edge Node
        -> Map Node Name
        -> Map Node [Node]
        -> Map Node [Edge]
        -> [Message]
        -> Map Node [Message]
        -> BpmnGraph
mkGraph n ns es catN catE sourceE targetE nameN containN containE messages messageN
  = let graph = BpmnGraph n
                          ns
                          es
                          catN
                          catE
                          sourceE
                          targetE
                          nameN
                          containN
                          containE
                          messages
                          messageN
    in  graph

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
        , allValidSubProcess -- \forall n \in N^{SubProcess} \union N^{Process} . n \in dom(containN) \wedge n \in dom(containE)
        , allValidContainers -- \forall n \in dom(containN) \union dom(containE) . n \in N^{SubProcess} \union N^{Process}
        , allValidMessageNodes -- \forall n \in N^{ST,RT,TMIE,CMIE,MSE,MEE} . n \in dom(messageN)
        , allValidMessagesForNodes -- \forall n \in dom(messageN) . \forall m \in messageN(n) . m \in messages
        ]
    <*> [g]

allValidMessagesForNodes :: BpmnGraph -> Bool
allValidMessagesForNodes _ = True -- TODO:

isValidMessageNode :: BpmnGraph -> Node -> Bool
isValidMessageNode g n = n `elem` dom_messageN
  where dom_messageN = keys $ messageN g

allValidMessageNodes :: BpmnGraph -> Bool
allValidMessageNodes g = getAll $ foldMap (All . isValidMessageNode g) ns
 where
  ns = nodesTs
    g
    [ SendTask
    , ReceiveTask
    , ThrowMessageIntermediateEvent
    , CatchMessageIntermediateEvent
    , MessageStartEvent
    , MessageEndEvent
    ]

isValidContainer :: BpmnGraph -> Node -> Bool
isValidContainer g n = n `elem` nodesTs g [SubProcess, Process]

allValidContainers :: BpmnGraph -> Bool
allValidContainers g = getAll $ foldMap (All . isValidContainer g) ns
 where
  ns    = keysN ++ keysE
  keysN = keys $ containN g
  keysE = keys $ containE g

isValidSubProcess :: BpmnGraph -> Node -> Bool
isValidSubProcess g n = n `elem` dom_containN && n `elem` dom_containE
 where
  dom_containN = keys $ containN g
  dom_containE = keys $ containE g

allValidSubProcess :: BpmnGraph -> Bool
allValidSubProcess g = getAll $ foldMap (All . isValidSubProcess g) ns
  where ns = nodesTs g [SubProcess, Process]

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
      Nothing -> False
      Just (cs, ct) ->
        (cs == SendTask || cs == ThrowMessageIntermediateEvent || cs == MessageEndEvent)
          && (ct == ReceiveTask || ct == CatchMessageIntermediateEvent || ct == MessageStartEvent)

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
