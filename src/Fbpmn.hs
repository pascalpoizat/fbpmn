{-# LANGUAGE DeriveGeneric #-}
module Fbpmn where

import           Data.Aeson                     ( encode
                                                , decode
                                                , FromJSON
                                                , ToJSON
                                                )
import qualified Data.ByteString.Lazy          as BS
import Data.Map.Strict ((!?))
import System.IO.Error (IOError,catchIOError,isDoesNotExistError)

--
-- JSON IO
--

{-|
Generate the JSON representation for a component instance.
-}
genJSON :: BpmnGraph -> BS.ByteString
genJSON = encode

{-|
Read a component instance from a JSON file.
-}
readFromJSON :: FilePath -> IO (Maybe BpmnGraph)
readFromJSON p = (decode <$> BS.readFile p) `catchIOError` handler
 where
  handler :: IOError -> IO (Maybe BpmnGraph)
  handler e
    | isDoesNotExistError e = do
      putTextLn "file not found"
      pure Nothing
    | otherwise = do
      putTextLn "unknown error"
      pure Nothing

{-|
Write a component instance to a JSON file.
-}
writeToJSON :: FilePath -> BpmnGraph -> IO ()
writeToJSON p = BS.writeFile p . encode

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

isInGraph :: (Ord a) => BpmnGraph
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
type Message = Text

--
-- Processes
--
type Process = Int

--
-- XML Ids
--
type Id = Text

--
-- Names
--
type Name = Text

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
data BpmnGraph = BpmnGraph { nodes :: [Node]
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

mkGraph :: [Node]
        -> [Edge]
        -> Map Node NodeType
        -> Map Node EdgeType
        -> Map Edge Node
        -> Map Edge Node
        -> Map Node Name
        -> BpmnGraph
mkGraph ns es catN catE sourceE targetE nameN =
  let graph = BpmnGraph ns es catN catE sourceE targetE nameN in graph

--
-- nodesT
-- nodesT g t = [ n | n <- nodes g, cat n == Just t ] where cat = catN g
--
nodesT :: BpmnGraph -> NodeType -> [Node]
nodesT g t = filter' (nodes g) (catN g) (== Just t)

--
-- nodesE
--
edgesT :: BpmnGraph -> EdgeType -> [Edge]
edgesT g t = filter' (edges g) (catE g) (== Just t)

--
-- helper
--
filter' :: (Ord a) => [a] -> (Map a b) -> (Maybe b -> Bool) -> [a]
filter' xs f p = filter p' xs
  where
    p' x = p $ f !? x

--
-- in
--
inN :: BpmnGraph -> Node -> [Edge]
inN g n = [ e | e <- edges g, target !? e == Just n ] where target = targetE g

--
-- out
--
outN :: BpmnGraph -> Node -> [Edge]
outN g n = [ e | e <- edges g, source !? e == Just n ] where source = sourceE g

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
    $   [ allNodesHave catN
        , allEdgesHave catE
        , allEdgesHave sourceE
        , allEdgesHave targetE
        ]
    <*> [g]

allNodesHave :: (BpmnGraph -> Map Node b) -> BpmnGraph -> Bool
allNodesHave = allDefF nodes

allEdgesHave :: (BpmnGraph -> Map Edge b) -> BpmnGraph -> Bool
allEdgesHave = allDefF edges

allDefF :: (Ord a, Foldable t, Functor t)
        => (BpmnGraph -> t a)
        -> (BpmnGraph -> Map a  b)
        -> BpmnGraph
        -> Bool
allDefF h f g = allDef (h g) f g

allDef :: (Ord a, Foldable t, Functor t)
       => t a
       -> (BpmnGraph -> Map a b)
       -> BpmnGraph
       -> Bool
allDef xs f g = not $ any isNothing $ (m !?) <$> xs
  where m = f g
