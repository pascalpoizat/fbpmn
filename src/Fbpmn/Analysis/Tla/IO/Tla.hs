{-# LANGUAGE QuasiQuotes #-}
module Fbpmn.Analysis.Tla.IO.Tla where

import qualified Data.Text         as T
import           Fbpmn.Helper
import           Fbpmn.BpmnGraph.Model
import           NeatInterpolation (text)
-- import           Data.List                      ( intercalate )
import           Data.Map.Strict   ((!?), foldrWithKey)

{-|
Write a BPMN Graph to a TLA+ file.
-}
writeToTLA :: FilePath -> Maybe a -> BpmnGraph -> IO ()
writeToTLA p _ = writeFile p . toString . encodeBpmnGraphToTla

{-|
Transform a BPMN Graph to a TLA specification.
-}
encodeBpmnGraphToTla :: BpmnGraph -> Text
encodeBpmnGraphToTla g =
  unlines
    $   [ encodeBpmnGraphHeaderToTla          -- header
        , encodeBpmnInterestToTla             -- interest
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
  ASSUME WF!WellTyped
  ASSUME WF!WellFormedness
  
  ConstraintNode == TRUE \* none
  ConstraintEdge == TRUE \* none
  Constraint == TRUE     \* none
  INSTANCE PWSConstraints
  
  INSTANCE PWSSemantics

  ================================================================
  |]

encodeBpmnInterestToTla :: BpmnGraph -> Text
encodeBpmnInterestToTla g =
  [text|
  Interest ==
    $interests
  |]
  where
    interests = T.intercalate "@@ " $ mapMap showRel (containN g)
    showRel :: Node -> Maybe [Node] -> Maybe Text
    showRel _ Nothing = Nothing
    showRel n (Just _) =
      case catN g !? n of 
        Nothing -> Nothing
        Just Process ->
          Just [text|
            $sn :> { $sns }
          |]
          where
            sn = show n
            sns = T.intercalate ", " $ show <$> interestedIn 
            interestedIn =
                foldrWithKey (\e m l -> if (targetInContainer (targetE g !? e) n) then m:l else l ) [] (messageE g)
                where
                targetInContainer :: Maybe Node -> Node -> Bool
                targetInContainer Nothing _ = False
                targetInContainer (Just target) container = 
                  case containN g !? container of
                    Nothing -> False
                    Just nodes ->
                      let subprocesses = foldr (\node l -> if (catN g !? node) == (Just SubProcess) then node:l else l) [] nodes in
                      elem target nodes || or (map (targetInContainer (Just target)) subprocesses)
        Just _ -> Nothing



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
  ns = relationTla nodeToNodeCatDecl (nodes g)
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
  es = relationTla edgeToEdgeCatDecl (edges g)
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
  es = relationTla edgeToEdgeSourceDecl (edges g)
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
  es = relationTla edgeToEdgeTargetDecl (edges g)
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
    spres = relationTla preToTla pres
    preToTla (n, e, es) = [text|<<$sn, $se>> :> {$ses}|]
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
    BoundaryEvent ==
    $sbes
  |]
  where
    sbes = relationTla beToTla bes
    beToTla e =
      case (catN g !? e, attached g !? e) of
        (Just (MessageBoundaryEvent v), Just spid) ->
          [text|$side :> [ attachedTo |-> $sspid, cancelActivity |-> $scae ]|]
          where
            side = show e
            sspid = show spid
            scae = if v then trueTla else falseTla
        (Just (TimerBoundaryEvent v), Just spid) ->
          [text|$side :> [ attachedTo |-> $sspid, cancelActivity |-> $scae ]|]
          where
            side = show e
            sspid = show spid
            scae = if v then trueTla else falseTla
        _ -> ""
    bes = nodesTs g $ [MessageBoundaryEvent,TimerBoundaryEvent] <*> [True, False]

trueTla :: Text
trueTla = "TRUE"

falseTla :: Text
falseTla = "FALSE"

emptySetTla :: Text
emptySetTla = "  [ i \\in {} |-> {}]"

relationTla :: (a -> Text) -> [a] -> Text
relationTla f xs =
  if null xs
  then emptySetTla
  else "   " <> T.intercalate "@@ " (f <$> xs)

nodeTypeToTLA :: NodeType -> Text
nodeTypeToTLA AbstractTask                  = "AbstractTask"
nodeTypeToTLA SendTask                      = "SendTask"
nodeTypeToTLA ReceiveTask                   = "ReceiveTask"
nodeTypeToTLA ThrowMessageIntermediateEvent = "ThrowMessageIntermediateEvent"
nodeTypeToTLA CatchMessageIntermediateEvent = "CatchMessageIntermediateEvent"
nodeTypeToTLA TimerIntermediateEvent        = "TimerIntermediateEvent"
nodeTypeToTLA (MessageBoundaryEvent _)      = "MessageBoundaryEvent"
nodeTypeToTLA (TimerBoundaryEvent _)        = "TimerBoundaryEvent"
nodeTypeToTLA SubProcess     = "SubProcess"
nodeTypeToTLA XorGateway     = "ExclusiveOr"
nodeTypeToTLA OrGateway      = "InclusiveOr"
nodeTypeToTLA AndGateway     = "Parallel"
nodeTypeToTLA EventBasedGateway = "EventBased"
nodeTypeToTLA NoneStartEvent = "NoneStartEvent"
nodeTypeToTLA MessageStartEvent = "MessageStartEvent"
nodeTypeToTLA TimerStartEvent = "TimerStartEvent"
nodeTypeToTLA NoneEndEvent      = "NoneEndEvent"
nodeTypeToTLA TerminateEndEvent = "TerminateEndEvent"
nodeTypeToTLA MessageEndEvent   = "MessageEndEvent"
nodeTypeToTLA Process           = "Process"

edgeTypeToTLA :: EdgeType -> Text
edgeTypeToTLA NormalSequenceFlow      = "NormalSeqFlow"
edgeTypeToTLA ConditionalSequenceFlow = "ConditionalSeqFlow"
edgeTypeToTLA DefaultSequenceFlow = "DefaultSeqFlow"
edgeTypeToTLA MessageFlow = "MessageFlow"
