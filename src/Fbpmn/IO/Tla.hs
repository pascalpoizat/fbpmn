{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.IO.Tla where

import qualified Data.Text         as T
import           Fbpmn.Model
import           Fbpmn.Helper
import           NeatInterpolation (text)
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict   ((!?))

{-|
Write a BPMN Graph to a TLA+ file.
-}
writeToTLA :: FilePath -> BpmnGraph -> IO ()
writeToTLA p = writeFile p . encodeBpmnGraphToTla

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToTla :: BpmnGraph -> Text
encodeBpmnGraphToTla g =
  unlines
    $   [ encodeBpmnGraphHeaderToTla          -- header
        , encodeBpmnGraphContainRelToTla      -- containment relation
        , encodeBpmnGraphNodeDeclToTla        -- nodes
        , encodeBpmnGraphEdgeDeclToTla        -- edges
        , encodeBpmnGraphMsgDeclToTla         -- messages
        , encodeBpmnGraphEdgeSourceDeclToTla  -- edge sources
        , encodeBpmnGraphEdgeTargetDeclToTla  -- edge targets
        , encodeBpmnGraphCatNToTla            -- node categories
        , encodeBpmnGraphCatEToTla            -- edge categories
        , encodeBpmnGraphFooterToTla          -- footer
        ]
    <*> [g]

encodeBpmnGraphHeaderToTla :: BpmnGraph -> Text
encodeBpmnGraphHeaderToTla g =
  [text|
  ---------------- MODULE $n ----------------

  EXTENDS TLC, PWSTypes

  VARIABLES nodemarks, edgemarks, net

  |]
  where
    n = name g

encodeBpmnGraphFooterToTla :: BpmnGraph -> Text
encodeBpmnGraphFooterToTla _ =
  [text|
  WF == INSTANCE PWSWellFormed
  ASSUME WF!WellFormedness
  
  INSTANCE PWSSemantics
  
  ================================================================
  |]

encodeBpmnGraphContainRelToTla :: BpmnGraph -> Text
encodeBpmnGraphContainRelToTla g =
  [text|
    ContainRel ==
      $crs
  |]
  where
    crs = T.intercalate "@@ " $ mapMap showRel (containN g)
    showRel :: Node -> Maybe [Node] -> Maybe Text
    showRel _ Nothing = Nothing
    showRel n (Just ns) =
      Just [text|
        $sn :> { $sns }
      |]
      where
        sn = show n
        sns = T.intercalate ", " $ show <$> ns

encodeBpmnGraphNodeDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphNodeDeclToTla g =
  [text|
    Node == {
      $ns
    }
  |]
  where
    ns = T.intercalate "," nodeDecls
    nodeDecls = show <$> nodes g

encodeBpmnGraphEdgeDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeDeclToTla g =
  [text|
    Edge == {
      $es
    }
  |]
  where
    es = T.intercalate "," edgeDecls
    edgeDecls = show <$> edges g

encodeBpmnGraphMsgDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphMsgDeclToTla g =
  [text|
    Message == { $msgs }

    msgtype ==
      $mts

  |]
  where
    msgs = T.intercalate ", " (show <$> messages g)
    mts = "    " <> T.intercalate "@@ " (edgeToMsgDecl <$> (edgesT g MessageFlow))
    edgeToMsgDecl e = case messageE g !? e of
      Nothing -> ""
      Just m -> [text|$e' :> $m'|]
        where
          m' = show m
          e' = show e
 
encodeBpmnGraphCatNToTla :: BpmnGraph -> Text
encodeBpmnGraphCatNToTla g = 
  [text|
    CatN ==
    $ns
  |]
 where
  ns = "   " <> T.intercalate "@@ " (nodeToNodeCatDecl <$> nodes g)
  nodeToNodeCatDecl n = case catN g !? n of
    Nothing -> ""
    Just c  -> [text|$n' :> $c'|] 
      where
        c' = nodeToTLA c
        n' = show n

encodeBpmnGraphCatEToTla :: BpmnGraph -> Text
encodeBpmnGraphCatEToTla g =
  [text|
    CatE ==
    $es
  |]
 where
  es = "   " <> T.intercalate "@@ " (edgeToEdgeCatDecl <$> edges g)
  edgeToEdgeCatDecl e = case catE g !? e of
    Nothing -> ""
    Just c  -> [text|$e' :> $c'|] 
      where
        c' = edgeToTLA c
        e' = show e

encodeBpmnGraphEdgeSourceDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeSourceDeclToTla g =
  [text|
    source ==
    $es
  |]
 where
  es = "   " <> T.intercalate "@@ " (edgeToEdgeSourceDecl <$> edges g)
  edgeToEdgeSourceDecl e = case sourceE g !? e of
    Nothing -> ""
    Just c  -> [text|$e' :> $c'|] 
      where
        c' = show c
        e' = show e

encodeBpmnGraphEdgeTargetDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeTargetDeclToTla g =
  [text|
    target ==
    $es
  |]
 where
  es = "   " <> T.intercalate "@@ " (edgeToEdgeTargetDecl <$> edges g)
  edgeToEdgeTargetDecl e = case sourceE g !? e of
    Nothing -> ""
    Just c  -> [text|$e' :> $c'|] 
      where
        c' = show c
        e' = show e

nodeToTLA :: NodeType -> Text
nodeToTLA AbstractTask   = "AbstractTask"
nodeToTLA SendTask       = "SendTask"
nodeToTLA ReceiveTask    = "ReceiveTask"
nodeToTLA ThrowMessageIntermediateEvent = "ThrowMessageIntermediateEvent"
nodeToTLA CatchMessageIntermediateEvent = "CatchMessageIntermediateEvent"
nodeToTLA SubProcess     = "SubProcess"
nodeToTLA XorGateway     = "ExclusiveOr"
nodeToTLA OrGateway      = "InclusiveOr"
nodeToTLA AndGateway     = "Parallel"
nodeToTLA EventBasedGateway = "EventBasedGateway"
nodeToTLA NoneStartEvent = "NoneStartEvent"
nodeToTLA MessageStartEvent = "MessageStartEvent"
nodeToTLA NoneEndEvent      = "NoneEndEvent"
nodeToTLA TerminateEndEvent = "TerminateEndEvent"
nodeToTLA MessageEndEvent   = "MessageEndEvent"
nodeToTLA Process           = "Process"

edgeToTLA :: EdgeType -> Text
edgeToTLA NormalSequenceFlow = "NormalSeqFlow"
edgeToTLA ConditionalSequenceFlow = "NormalSeqFlow"
edgeToTLA DefaultSequenceFlow = "NormalSeqFlow"
edgeToTLA MessageFlow = "MsgFlow"
