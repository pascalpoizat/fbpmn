{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.IO.Tla where

import qualified Data.Text         as T
import           Fbpmn.Helper
import           Fbpmn.Model
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
        , encodeBpmnGraphPreEToTla            -- preE relation
        , encodeBpmnGraphPreNToTla            -- preN relation
        , encodeBpmnBoundaryEventsToTla       -- information about boundary events
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
    mts = if null (messages g) then emptySetTla else "    " <> T.intercalate "@@ " (edgeToMsgDecl <$> (edgesT g MessageFlow))
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
        c' = nodeTypeToTLA c
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
        c' = edgeTypeToTLA c
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
  edgeToEdgeTargetDecl e = case targetE g !? e of
    Nothing -> ""
    Just c  -> [text|$e' :> $c'|]
      where
        c' = show c
        e' = show e

encodeBpmnGraphPreEToTla :: BpmnGraph -> Text
encodeBpmnGraphPreEToTla g =
  [text|
  LOCAL preEdges ==
  $spres
  PreEdges(n,e) == preEdges[n,e]
  |]
  where
    gws = nodesT g OrGateway
    spres = if null pres then emptySetTla else T.intercalate "@@ " $ preToTLA <$> pres
    preToTLA (n, e, es) = [text|<<$sn, $se>> :> {$ses}|]
      where
        sn = show n
        se = show e
        ses = T.intercalate ", " $ show <$> es
    pres = concat $ preE' g <$> gws
    preE' g' n = [ (n, e, preE g' n e) | e <- inNTs g' n sequenceFlow ]

encodeBpmnGraphPreNToTla :: BpmnGraph -> Text
encodeBpmnGraphPreNToTla _ =
  [text|
  PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
            \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }
  |]

encodeBpmnBoundaryEventsToTla :: BpmnGraph -> Text
encodeBpmnBoundaryEventsToTla g =
  [text|
    CABoundaries ==
    $scabes

    ATBoundaries ==
    $satbes
  |]
  where
    scabes = if null bes
              then emptySetTla
              else "   " <> T.intercalate "@@ " (cabeToTla <$> bes)
    satbes = if null bes
              then emptySetTla
              else "   " <> T.intercalate "@@ " (atbeToTla <$> bes)
    atbeToTla _ = undefined -- TODO:
    cabeToTla e = case catN g !? e of
      Just (MessageBoundaryEvent v) -> [text|$side :> $scae|]
        where
          side = show e
          scae = show v
      _ -> ""
    bes = nodesTs g $ [MessageBoundaryEvent] <*> [True, False]

emptySetTla :: Text
emptySetTla = "  [ i \\in {} |-> {}]"

nodeTypeToTLA :: NodeType -> Text
nodeTypeToTLA AbstractTask                  = "AbstractTask"
nodeTypeToTLA SendTask                      = "SendTask"
nodeTypeToTLA ReceiveTask                   = "ReceiveTask"
nodeTypeToTLA ThrowMessageIntermediateEvent = "ThrowMessageIntermediateEvent"
nodeTypeToTLA CatchMessageIntermediateEvent = "CatchMessageIntermediateEvent"
nodeTypeToTLA (MessageBoundaryEvent _)      = "MessageBoundaryEvent"
nodeTypeToTLA SubProcess                    = "SubProcess"
nodeTypeToTLA XorGateway                    = "ExclusiveOr"
nodeTypeToTLA OrGateway                     = "InclusiveOr"
nodeTypeToTLA AndGateway                    = "Parallel"
nodeTypeToTLA EventBasedGateway             = "EventBasedGateway"
nodeTypeToTLA NoneStartEvent                = "NoneStartEvent"
nodeTypeToTLA MessageStartEvent             = "MessageStartEvent"
nodeTypeToTLA NoneEndEvent                  = "NoneEndEvent"
nodeTypeToTLA TerminateEndEvent             = "TerminateEndEvent"
nodeTypeToTLA MessageEndEvent               = "MessageEndEvent"
nodeTypeToTLA Process                       = "Process"

edgeTypeToTLA :: EdgeType -> Text
edgeTypeToTLA NormalSequenceFlow      = "NormalSeqFlow"
edgeTypeToTLA ConditionalSequenceFlow = "ConditionalSeqFlow"
edgeTypeToTLA DefaultSequenceFlow     = "DefaultSeqFlow"
edgeTypeToTLA MessageFlow             = "MsgFlow"
