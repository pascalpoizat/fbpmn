{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.IO.Dot where

import           Fbpmn.Model
import           NeatInterpolation (text)
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict   ((!?))

{-|
Write a BPMN Graph to a DOT file.
-}
writeToDOT :: FilePath -> BpmnGraph -> IO ()
writeToDOT p = writeFile p . encodeBpmnGraphToDot

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToDot :: BpmnGraph -> Text
encodeBpmnGraphToDot g =
  unlines
    $   [ encodeBpmnGraphHeaderToDot    -- header
        -- , encodeBpmnGraphNodeDeclToDot        -- nodes
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
