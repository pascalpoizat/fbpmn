{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.BpmnGraph.IO.Dot where

import           Fbpmn.BpmnGraph.Model
import           NeatInterpolation (text)
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict   ((!?))
import Fbpmn.Helper (FWriter(FW))

-- | FWriter from BPMN Graph to DOT.
writer :: FWriter BpmnGraph
writer = FW writeToDOT ".dot" 

{-|
Write a BPMN Graph to a DOT file.
-}
writeToDOT :: FilePath -> BpmnGraph -> IO ()
writeToDOT p = writeFile p . toString . encodeBpmnGraphToDot

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToDot :: BpmnGraph -> Text
encodeBpmnGraphToDot g =
  unlines
    $   [ encodeBpmnGraphHeaderToDot    -- header
        , encodeBpmnGraphNodeDeclToDot  -- nodes
        , encodeBpmnGraphEdgeDeclToDot  -- edges
        , encodeBpmnGraphFooterToDot    -- footer
        ]
    <*> [g]

encodeBpmnGraphHeaderToDot :: BpmnGraph -> Text
encodeBpmnGraphHeaderToDot g =
  [text|digraph "$n" {
  |]
  where
    n = name g

encodeBpmnGraphFooterToDot :: BpmnGraph -> Text
encodeBpmnGraphFooterToDot _ =
  [text|}
  |]

encodeBpmnGraphNodeDeclToDot :: BpmnGraph -> Text
encodeBpmnGraphNodeDeclToDot g =
  [text|
  $nes
  |]
  where
    nes = unlines $ toDot <$> nodes g
    toDot n =
      [text|
      $sn [ $reprn ];
      |]
      where
        sn = show n
        reprn = nodeRepresentation (catN g !? n) (nameOrElseIdForNode g n)

nodeRepresentation :: Maybe NodeType -> (Node, String) -> Text
nodeRepresentation (Just AndGateway) _ = [text|label = "+", shape = "diamond"|]
nodeRepresentation (Just XorGateway) _ = [text|label = "x", shape = "diamond"|]
nodeRepresentation (Just OrGateway ) _ = [text|label = "o", shape = "diamond"|]
nodeRepresentation (Just EventBasedGateway) _ =
  [text|label = "@", shape = "diamond"|]
nodeRepresentation (Just NoneStartEvent) _ =
  [text|label = "", shape = "circle"|]
nodeRepresentation (Just MessageStartEvent) _ =
  [text|label = "??", shape = "circle"|]
nodeRepresentation (Just TimerStartEvent) _ =
  [text|label = "??", shape = "circle"|]
nodeRepresentation (Just CatchMessageIntermediateEvent) _ =
  [text|label = "??", shape = "doublecircle"|]
nodeRepresentation (Just ThrowMessageIntermediateEvent) _ =
  [text|label = "!!", shape = "doublecircle"|]
nodeRepresentation (Just TimerIntermediateEvent) _ =
  [text|label = "!!", shape = "doublecircle"|]
nodeRepresentation (Just NoneEndEvent) _ = [text|label = "", shape = "circle"|]
nodeRepresentation (Just MessageEndEvent) _ =
  [text|label = "!!", shape = "circle"|]
nodeRepresentation (Just TerminateEndEvent) _ =
  [text|label = "T", shape = "circle"|]
nodeRepresentation (Just SendTask) (_, x) = [text|label = $l, shape = "box" |]
  where l = show $ "!! " <> x
nodeRepresentation (Just _) (_, x) = [text|label = $sx, shape = "box"|]
  where sx = show x
nodeRepresentation Nothing (_, x) = [text|label = $sx, shape = "box"|]
  where sx = show x

nameOrElseIdForNode :: BpmnGraph -> Node -> (Node, String)
nameOrElseIdForNode g n = (n, fromMaybe n $ nameN g !? n)

encodeBpmnGraphEdgeDeclToDot :: BpmnGraph -> Text
encodeBpmnGraphEdgeDeclToDot g =
  [text|
  $tes
  |]
  where
    tes = unlines $ toDot <$> edges g
    toDot e =
      case
        do
          source <- sourceE g !? e
          target <- targetE g !? e
          cat <- catE g !? e
          pure (source, target, cat)
        of
          Nothing -> ""
          Just (s,t,c) -> edgeToDot s t c

edgeToDot :: Node -> Node -> EdgeType -> Text
edgeToDot s t c =
          let
              ss = show s
              st = show t
          in
              if c == MessageFlow
                then [text|$ss -> $st [style=dashed];|]
                else [text|$ss -> $st;|]
