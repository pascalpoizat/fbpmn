{-# LANGUAGE QuasiQuotes #-}

module Fbpmn.Analysis.Tla.IO.Tla where

-- import           Data.List                      ( intercalate )
import Data.Map.Strict (foldrWithKey, keys, (!?))
import Data.Map.Strict as M (fromList)
import qualified Data.Text as T
import Fbpmn.BpmnGraph.Model
import Fbpmn.BpmnGraph.SpaceModel
import Fbpmn.Helper
import NeatInterpolation (text)

-- |
-- Write a BPMN Graph to a TLA+ file.
writeToTLA :: FilePath -> Maybe a -> BpmnGraph -> IO ()
writeToTLA p _ = writeFile p . toString . encodeBpmnGraphToTla

-- |
-- Write a Space BPMN Graph to a TLA+ file.
writeToSTLA :: FilePath -> Maybe a -> SpaceBpmnGraph -> IO ()
writeToSTLA p _ = writeFile p . toString . encodeSBpmnGraphToTla

-- |
-- Transform a BPMN Graph to a TLA specification.
encodeBpmnGraphToTla :: BpmnGraph -> Text
encodeBpmnGraphToTla g =
  unlines $
    [ encodeBpmnGraphHeaderToTla, -- header
      encodeBpmnInterestToTla, -- interest
      encodeBpmnGraphContainRelToTla, -- containment relation
      encodeBpmnGraphNodeDeclToTla, -- nodes
      encodeBpmnGraphEdgeDeclToTla, -- edges
      encodeBpmnGraphMsgDeclToTla, -- messages
      encodeBpmnGraphEdgeSourceDeclToTla, -- edge sources
      encodeBpmnGraphEdgeTargetDeclToTla, -- edge targets
      encodeBpmnGraphCatNToTla, -- node categories
      encodeBpmnGraphCatEToTla, -- edge categories
      encodeBpmnGraphPreEToTla, -- preE relation
      encodeBpmnGraphPreNToTla, -- preN relation
      encodeBpmnBoundaryEventsToTla, -- information about boundary events
      encodeBpmnGraphFooterToTla -- footer
    ]
      <*> [g]

-- |
-- Transform a BPMN Graph to a TLA specification.
encodeSBpmnGraphToTla :: SpaceBpmnGraph -> Text
encodeSBpmnGraphToTla g =
  unlines $
    [ encodeSBpmnGraphHeaderToTla, -- header (EXTENSION)
      encodeBpmnInterestToTla . graph, -- interest
      encodeBpmnGraphContainRelToTla . graph, -- containment relation
      encodeBpmnGraphNodeDeclToTla . graph, -- nodes
      encodeBpmnGraphEdgeDeclToTla . graph, -- edges
      encodeBpmnGraphMsgDeclToTla . graph, -- messages
      encodeBpmnGraphEdgeSourceDeclToTla . graph, -- edge sources
      encodeBpmnGraphEdgeTargetDeclToTla . graph, -- edge targets
      encodeBpmnGraphCatNToTla . graph, -- node categories
      encodeBpmnGraphCatEToTla . graph, -- edge categories
      encodeBpmnGraphPreEToTla . graph, -- preE relation
      encodeBpmnGraphPreNToTla . graph, -- preN relation
      encodeBpmnBoundaryEventsToTla . graph, -- information about boundary events
      encodeSExtensionToTla, -- space BPMN information (EXTENSION)
      encodeBpmnGraphFooterToTla . graph -- footer
    ]
      <*> [g]

encodeSExtensionToTla :: SpaceBpmnGraph -> Text
encodeSExtensionToTla g =
  unlines $
    [ encodeSStructure . spacestructure,
      encodeGList "Var" variables,
      encodeVarLoc,
      encodeLocVar,
      encodeSConditions,
      encodeSActions,
      encodeSEvalF,
      encodeSEvalA,
      encodeSInit
    ]
      <*> [g]

genLocName :: Node -> String
genLocName n = "loc" <> n

encodeVarLoc :: SpaceBpmnGraph -> Text
encodeVarLoc s = encodeMap show show "varloc" ns (M.fromList $ zip ns vs)
  where
    ns = ((`nodesT` Process) . graph) s
    vs = genLocName <$> ns

encodeLocVar :: SpaceBpmnGraph -> Text
encodeLocVar s = encodeMap show show "locvar" vs (M.fromList $ zip vs ns)
  where
    ns = ((`nodesT` Process) . graph) s
    vs = genLocName <$> ns

encodeSConditions :: SpaceBpmnGraph -> Text
encodeSConditions g = "" -- undefined -- TODO:

encodeSActions :: SpaceBpmnGraph -> Text
encodeSActions g = "" -- undefined -- TODO:

encodeSEvalF :: SpaceBpmnGraph -> Text
encodeSEvalF g = "" -- undefined -- TODO:

encodeSEvalA :: SpaceBpmnGraph -> Text
encodeSEvalA g = "" -- undefined -- TODO:

encodeSInit :: SpaceBpmnGraph -> Text
encodeSInit g = "" -- undefined -- TODO:

encodeSStructure :: SpaceStructure -> Text
encodeSStructure s =
  unlines $
    [ encodeGList "BaseLocation" baseLocations,
      encodeGList "GroupLocation" groupLocations,
      encodeSLocations,
      encodeGList "SpaceEdge" sEdges,
      encodeGMap show show "SpaceSource" sEdges sSourceE,
      encodeGMap show show "SpaceTarget" sEdges sTargetE
    ]
      <*> [s]
  where
    encodeSLocations _ =
      [text|
      Locations == GroupLocation \union BaseLocation
      |]

encodeSBpmnGraphHeaderToTla :: SpaceBpmnGraph -> Text
encodeSBpmnGraphHeaderToTla g =
  [text|
  ---------------- MODULE $n ----------------

  EXTENDS TLC, PWSTypes

  VARIABLES nodemarks, edgemarks, net, subs, sigma

  |]
  where
    n = name . graph $ g

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
          Just
            [text|
            $sn :> { $sns }
          |]
          where
            sn = show n
            sns = T.intercalate ", " . hashNub $ show <$> interestedIn
            interestedIn =
              foldrWithKey (\e m l -> if targetInContainer (targetE g !? e) n then m : l else l) [] (messageE g)
              where
                targetInContainer :: Maybe Node -> Node -> Bool
                targetInContainer Nothing _ = False
                targetInContainer (Just target) container =
                  case containN g !? container of
                    Nothing -> False
                    Just nodes ->
                      let subprocesses = foldr (\node l -> if (catN g !? node) == Just SubProcess then node : l else l) [] nodes
                       in elem target nodes || any (targetInContainer (Just target)) subprocesses
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
      Just
        [text|
        $sn :> { $sns }
      |]
      where
        sn = show n
        sns = T.intercalate ", " $ show <$> ns

encodeBpmnGraphNodeDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphNodeDeclToTla = encodeGList "Node" nodes

encodeBpmnGraphEdgeDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeDeclToTla = encodeGList "Edge" edges

encodeBpmnGraphMsgDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphMsgDeclToTla g =
  unlines $
    [ encodeBpmnGraphMessagesToTla,
      encodeBpmnGraphMessageTypesToTla
    ]
      <*> [g]
  where
    encodeBpmnGraphMessagesToTla = encodeGList "Message" messages
    encodeBpmnGraphMessageTypesToTla = encodeGMap show show "msgtype" (`edgesT` MessageFlow) messageE

encodeBpmnGraphCatNToTla :: BpmnGraph -> Text
encodeBpmnGraphCatNToTla = encodeGMap show nodeTypeToTLA "CatN" nodes catN

encodeBpmnGraphCatEToTla :: BpmnGraph -> Text
encodeBpmnGraphCatEToTla = encodeGMap show edgeTypeToTLA "CatE" edges catE

encodeBpmnGraphEdgeSourceDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeSourceDeclToTla = encodeGMap show show "source" edges sourceE

encodeBpmnGraphEdgeTargetDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeTargetDeclToTla = encodeGMap show show "target" edges targetE

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
    preE' g' n = [(n, e, preE g' n e) | e <- inNTs g' n sequenceFlow]

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
    bes = nodesTs g [MessageBoundaryEvent, TimerBoundaryEvent]
    beToTla e = case (catN g !? e, attached g !? e) of
      (Just MessageBoundaryEvent, Just spid) ->
        [text|$side :> [ attachedTo |-> $sspid, cancelActivity |-> $scae ]|]
        where
          side = show e
          sspid = show spid
          scae = boolToTLA $ Just False /= (isInterrupt g !? e)
      (Just TimerBoundaryEvent, Just spid) ->
        [text|$side :> [ attachedTo |-> $sspid, cancelActivity |-> $scae ]|]
        where
          side = show e
          sspid = show spid
          scae = boolToTLA $ Just False /= (isInterrupt g !? e)
      (Just _, _) -> ""
      (Nothing, _) -> ""

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

encodeGList :: Show b => Text -> (a -> [b]) -> a -> Text
encodeGList n f x = encodeList n (f x)

encodeList :: Show a => Text -> [a] -> Text
encodeList n xs =
  [text|
  $n == { $sxs }
  |]
  where
    sxs = T.intercalate ", " $ show <$> xs

encodeGMap :: Ord b => (b -> Text) -> (c -> Text) -> Text -> (a -> [b]) -> (a -> Map b c) -> a -> Text
encodeGMap wa wb n f g x = encodeMap wa wb n (f x) (g x)

encodeMap' :: Ord a => (a -> Text) -> (b -> Text) -> Text -> Map a b -> Text
encodeMap' wa wb n m = encodeMap wa wb n (keys m) m

encodeMap :: Ord a => (a -> Text) -> (b -> Text) -> Text -> [a] -> Map a b -> Text
encodeMap wa wb n ks m =
  [text|
    $n ==
    $sxs
  |]
  where
    sxs = relationTla h ks
    h k = case m !? k of
      Nothing -> ""
      Just v -> [text|$k' :> $v'|]
        where
          v' = wb v
          k' = wa k

nodeTypeToTLA :: NodeType -> Text
nodeTypeToTLA AbstractTask = "AbstractTask"
-- start
nodeTypeToTLA NoneStartEvent = "NoneStartEvent"
-- end
nodeTypeToTLA NoneEndEvent = "NoneEndEvent"
nodeTypeToTLA TerminateEndEvent = "TerminateEndEvent"
-- gateways
nodeTypeToTLA XorGateway = "ExclusiveOr"
nodeTypeToTLA OrGateway = "InclusiveOr"
nodeTypeToTLA AndGateway = "Parallel"
nodeTypeToTLA EventBasedGateway = "EventBased"
-- structure
nodeTypeToTLA SubProcess = "SubProcess"
nodeTypeToTLA Process = "Process"
-- communication
nodeTypeToTLA MessageStartEvent = "MessageStartEvent"
nodeTypeToTLA SendTask = "SendTask"
nodeTypeToTLA ReceiveTask = "ReceiveTask"
nodeTypeToTLA ThrowMessageIntermediateEvent = "ThrowMessageIntermediateEvent"
nodeTypeToTLA CatchMessageIntermediateEvent = "CatchMessageIntermediateEvent"
nodeTypeToTLA MessageBoundaryEvent = "MessageBoundaryEvent"
nodeTypeToTLA MessageEndEvent = "MessageEndEvent"
-- time
nodeTypeToTLA TimerStartEvent = "TimerStartEvent"
nodeTypeToTLA TimerIntermediateEvent = "TimerIntermediateEvent"
nodeTypeToTLA TimerBoundaryEvent = "TimerBoundaryEvent"

edgeTypeToTLA :: EdgeType -> Text
edgeTypeToTLA NormalSequenceFlow = "NormalSeqFlow"
edgeTypeToTLA ConditionalSequenceFlow = "ConditionalSeqFlow"
edgeTypeToTLA DefaultSequenceFlow = "DefaultSeqFlow"
edgeTypeToTLA MessageFlow = "MessageFlow"

boolToTLA :: Bool -> Text
boolToTLA True = trueTla
boolToTLA False = falseTla