module Fbpmn.Model where

import           Data.Aeson                     ( FromJSON
                                                , ToJSON
                                                )
import           Data.Monoid                    ( All(..) )
import           Data.Maybe                     ( isNothing )
import           GHC.Generics
import           Data.Map.Strict                ( Map
                                                , (!?)
                                                )

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
