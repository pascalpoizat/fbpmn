{-# LANGUAGE QuasiQuotes #-}

module Fbpmn.Analysis.Tla.IO.Tla where

-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
-- import           Data.List                      ( intercalate )
import Data.Map.Strict (foldrWithKey, keys, (!?), mapWithKey, union)
import Data.Map.Strict as M (fromList)
import qualified Data.Text as T
import Fbpmn.BpmnGraph.Model
import Fbpmn.BpmnGraph.SpaceModel
import Fbpmn.Helper
import NeatInterpolation (text)
import Data.Containers.ListUtils (nubOrd)

-- | FWriter from BPMN Graph to TLA+.
writer :: FWriter BpmnGraph
writer = FW writeToTLA ".tla"

-- |
-- Write a BPMN Graph to a TLA+ file.
writeToTLA :: FilePath -> BpmnGraph -> IO ()
writeToTLA p = writeFile p . toString . encodeBpmnGraphToTla

-- | FWriter from Space BPMN Graph to TLA+.
writerS :: FWriter SpaceBpmnGraph
writerS = FW writeToSTLA ".tla"

-- |
-- Write a Space BPMN Graph to a TLA+ file.
writeToSTLA :: FilePath -> SpaceBpmnGraph -> IO ()
writeToSTLA p = writeFile p . toString . encodeSBpmnGraphToTla

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
encodeSBpmnGraphToTla s =
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
      <*> [s]

encodeSExtensionToTla :: SpaceBpmnGraph -> Text
encodeSExtensionToTla s =
  unlines $
    [ encodeSStructure . spacestructure,
      encodeGList show "Var" variables,
      encodeVarLoc,
      encodeLocVar,
      encodeReachability,
      encodeSConditions,
      encodeSActions,
      encodeCodeConditions,
      encodeSEvalF,
      encodeSInit
    ]
      <*> [s]

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

-- TODO: optimize
encodeReachability :: SpaceBpmnGraph -> Text
encodeReachability g = unlines
    [ encodeMap show (setTla show) "Reachable" (locs g) (computeReachabilityMap g)
    , encodeReachabilityDefs
    ]
  where
    computeReachabilityMap :: SpaceBpmnGraph -> Map BaseLocation [BaseLocation]
    computeReachabilityMap gr = M.fromList $ reach (spacestructure gr) <$> locs gr
    reach :: SpaceStructure -> BaseLocation -> (BaseLocation, [BaseLocation])
    reach s l = (l, listFixpoint (f s) [l])
    f :: SpaceStructure -> [BaseLocation] -> [BaseLocation]
    f s ls = nubOrd $ ls ++ concatMap (neighbours s) ls
    -- f :: SpaceStructure -> [BaseLocation] -> [BaseLocation] -> [BaseLocation]
    -- f _ [] rs = rs
    -- f s (b:bs) rs = f s bs' rs'
    --     where
    --       ns = neighbours s b -- neighbours of b, i.e., all n such that b -> n
    --       ns' = filter (`elem` (b:rs)) ns -- remove b and already treated locations, i.e., ns - {b} - rs
    --       bs' = nubOrd $ bs ++ ns'
    --       rs' = b:rs
    locs = baseLocations . spacestructure

encodeReachabilityDefs :: Text
encodeReachabilityDefs = [text|
  reachFrom(b) == UNION {Reachable[x] : x \in b}
|]

-- encodeReachability _ = [text|
--   outgoingSpace(n) == { e \in SpaceEdge : SpaceSource[e] = n } 

--   succSpa(n) == { SpaceTarget[e] : e \in outgoingSpace(n) } 

--   RECURSIVE succsNew(_, _, _)
--   succsNew (n, A, B) == IF UNION{B} \ UNION{A} = {} THEN B
--                                 ELSE LET s == CHOOSE s \in UNION{UNION{B} \ UNION{A}} : TRUE
--                                     IN succsNew(n, UNION{A \union {s}}, UNION{B \union UNION{succSpa(s)}}) 

--   succsSpace == [b \in BaseLocation |-> succsNew (b, {b}, succSpa(b))]

--   RECURSIVE nextLocs(_, _, _)
--   nextLocs (n, A, B) == IF UNION{B} \ UNION{A} = {} THEN B
--                                 ELSE LET s == CHOOSE s \in UNION{UNION{B} \ UNION{A}} : TRUE
--                                     IN nextLocs(n, UNION{A \union {s}}, UNION{B \union UNION{succsSpace[s]}}) 

--   reach(v,p) == nextLocs (v[varloc[p]], {v[varloc[p]]} , succsSpace[v[varloc[p]]])

--   reachFrom(v,p,x) == nextLocs (v[x], {v[x]} , succsSpace[v[x]])
-- |]

encodeSConditions :: SpaceBpmnGraph -> Text
encodeSConditions g =
  unlines $
    [ encodeCSFVar,
      encodeCSFKind,
      encodeCSFCond,
      encodeCSFFormula,
      encodeOrdering
    ]
      <*> [g]

encodeSActions :: SpaceBpmnGraph -> Text
encodeSActions g =
  unlines $
    [ encodeAKind,
      encodeAUpdateVar,
      encodeAUpdateGMinus,
      encodeAUpdateGPlus,
      encodeACond,
      encodeAFormula
    ]
      <*> [g]

encodeCSFVar :: SpaceBpmnGraph -> Text
encodeCSFVar g = encodeMap show show "cVar" (keys . cVariables $ g) (cVariables g)

encodeCSFKind :: SpaceBpmnGraph -> Text
encodeCSFKind g = encodeMap show fKindToTla "cKind" (keys . cKinds $ g) (cKinds g)
  where
    fKindToTla SFAll = "All"
    fKindToTla SFAny = "Some"

encodeCSFFormula :: SpaceBpmnGraph -> Text
encodeCSFFormula g = unlines $ encodeEdgeFormulaDef g <$> (keys . cFormulas $ g)

encodeAKind :: SpaceBpmnGraph -> Text
encodeAKind g = encodeMap show fKindToTla "aKind" (keys . actions $ g) (actions g)
  where
    fKindToTla SAPass = "ACT_PASS"
    fKindToTla SAMove {} = "ACT_MOVE"
    fKindToTla SAUpdate {} = "ACT_UPDATE"

encodeAUpdateVar :: SpaceBpmnGraph -> Text
encodeAUpdateVar g = encodeMap show f "aUpdateVar" (keys . filterValue isUpdateSpaceAction . actions $ g) (actions g)
  where
    f SAPass = ""
    f SAMove {} = ""
    f (SAUpdate v _ _ ) = show v

encodeAUpdateGMinus :: SpaceBpmnGraph -> Text
encodeAUpdateGMinus g = encodeMap show f "aUpdateGMinus" (keys . filterValue isUpdateSpaceAction . actions $ g) (actions g)
  where
    f SAPass = ""
    f SAMove {} = ""
    f (SAUpdate _ gm _ ) = setTla show gm

encodeAUpdateGPlus :: SpaceBpmnGraph -> Text
encodeAUpdateGPlus g = encodeMap show f "aUpdateGPlus" (keys . filterValue isUpdateSpaceAction . actions $ g) (actions g)
  where
    f SAPass = ""
    f SAMove {} = ""
    f (SAUpdate _ _ gp ) = setTla show gp

encodeAFormula :: SpaceBpmnGraph -> Text
encodeAFormula g = unlines $ encodeActionFormulaDef g <$> (keys . filterValue isMoveSpaceAction . actions $ g)

encodeCond :: Text -> (SpaceBpmnGraph -> [Id]) -> (SpaceBpmnGraph -> Map Id SpaceFormula) -> SpaceBpmnGraph -> Text
encodeCond t k f g = encodeMap show show t (k g) (mapWithKey genF $ f g)

encodeCSFCond :: SpaceBpmnGraph -> Text
-- encodeCSFCond g = encodeMap show show "cCond" (keys . cFormulas $ g) (mapWithKey genF $ identifiedCFormulas g)
encodeCSFCond = encodeCond "cCond" (keys . cFormulas) identifiedCFormulas

encodeACond :: SpaceBpmnGraph -> Text
-- encodeACond g = encodeMap show show "aCond" (keys . filterValue isMoveSpaceAction . actions $ g) (mapWithKey genF $ identifiedAFormulas g)
encodeACond = encodeCond "aCond" (keys . filterValue isMoveSpaceAction . actions) identifiedAFormulas

encodeOrdering :: SpaceBpmnGraph -> Text
encodeOrdering _ = [text|
  orderingSet == { }
  order(a,b) == <<a,b>> \in orderingSet
|]

genCode :: Text -> Text
genCode e = "f_" <> e

genF :: Edge -> SpaceFormula -> Text
genF e _ = genCode . toText $ e

encodeEdgeFormulaDef :: SpaceBpmnGraph -> Edge -> Text
encodeEdgeFormulaDef g e = [text|def_$es(v,s,p) == $def|]
  where
    es = genCode . toText $ e
    def = maybe falseTla encodeFormula (cFormulas g !? e)

encodeActionFormulaDef :: SpaceBpmnGraph -> Node -> Text
encodeActionFormulaDef g n = [text|def_$ns(v,s,p) == $def|]
  where
    ns = genCode . toText $ n
    def = maybe falseTla encodeFormula (saSpaceFormula =<< actions g !? n)

encodeFormula :: SpaceFormula -> Text
encodeFormula SFTrue = trueTla
encodeFormula SFHere = [text|v[varloc[p]]|]
encodeFormula (SFVar v) = [text|v[$sv]|]
  where sv = show v
encodeFormula (SFBase v) = [text|{ $vs }|]
  where vs = show v
encodeFormula (SFGroup v) = [text|s[$vs]|]
  where vs = show v
encodeFormula (SFNot f) = [text|(BaseLocation - $sf)|]
  where sf = encodeFormula f
encodeFormula (SFOr f1 f2 ) = [text|($sf1 \union $sf2)|]
  where
    sf1 = encodeFormula f1
    sf2 = encodeFormula f2
encodeFormula (SFAnd f1 f2 ) = [text|($sf1 \intersect $sf2)|]
  where
    sf1 = encodeFormula f1
    sf2 = encodeFormula f2
encodeFormula SFReach = [text|reachFrom(v[varloc[p]])|]
encodeFormula (SFReachFrom x) = [text|reachFrom(v[$xs])|]
  where xs = show x

identifiedCFormulas :: SpaceBpmnGraph -> Map Id SpaceFormula
identifiedCFormulas = cFormulas

identifiedAFormulas :: SpaceBpmnGraph -> Map Id SpaceFormula
identifiedAFormulas s = mapMaybes $ saSpaceFormula <$> actions s

identifiedFormulas :: SpaceBpmnGraph -> Map Id SpaceFormula
identifiedFormulas s = identifiedCFormulas s `union` identifiedAFormulas s

encodeSEvalF :: SpaceBpmnGraph -> Text
encodeSEvalF s =
  if null $ keys idfs
  then
    [text|evalF(v,s,p,f) == $emptySetTla|]
  else
    [text|evalF(v,s,p,f) ==
        $ifs
        ELSE $emptySetTla
    |]
      where
        idfs = identifiedFormulas s
        ifs = toText $ intercalate "ELSE " $ f <$> keys idfs
        f e = toString [text|IF f = "$se" THEN def_$se(v,s,p)|] where se = genCode . toText $ e

encodeCodeConditions :: SpaceBpmnGraph -> Text
encodeCodeConditions s = encodeList show "CodeCondition" . fmap genCode $ ids
  where
    ids = toText <$> keys (identifiedFormulas s)

encodeSInit :: SpaceBpmnGraph -> Text
encodeSInit s =
  unlines $
    [ encodeGMap show show "startloc" ((`nodesT` Process) . graph) (initialLocations . initial)
    , encodeGMap show (setTla show) "startsub" (groupLocations . spacestructure) (initialSpace . initial)
    ]
      <*> [s]

encodeSStructure :: SpaceStructure -> Text
encodeSStructure s =
  unlines $
    [ encodeGList show "BaseLocation" baseLocations,
      encodeGList show "GroupLocation" groupLocations,
      encodeSLocations,
      encodeGList show "SpaceEdge" sEdges,
      encodeGMap show show "SpaceSource" sEdges sSourceE,
      encodeGMap show show "SpaceTarget" sEdges sTargetE
    ]
      <*> [s]
  where
    encodeSLocations _ =
      [text|
      Location == GroupLocation \union BaseLocation
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

  VARIABLES nodemarks, edgemarks, net, lifecycle

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
  IntervalConstraint == TRUE     \* none

  INSTANCE PWSConstraints
  INSTANCE UserProperties
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
encodeBpmnGraphNodeDeclToTla = encodeGList show "Node" nodes

encodeBpmnGraphEdgeDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphEdgeDeclToTla = encodeGList show "Edge" edges

encodeBpmnGraphMsgDeclToTla :: BpmnGraph -> Text
encodeBpmnGraphMsgDeclToTla g =
  unlines $
    [ encodeBpmnGraphMessagesToTla,
      encodeBpmnGraphMessageTypesToTla
    ]
      <*> [g]
  where
    encodeBpmnGraphMessagesToTla = encodeGList show "Message" messages
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

emptyMapTla :: Text
emptyMapTla = "  [ i \\in {} |-> {}]"

emptySetTla :: Text
emptySetTla = "{  }"

setTla :: (a -> Text) -> [a] -> Text
setTla f xs = "{ " <> T.intercalate ", " (f <$> xs) <> " }"

relationTla :: (a -> Text) -> [a] -> Text
relationTla f xs =
  if null xs
    then emptyMapTla
    else "   " <> T.intercalate "@@ " (f <$> xs)

encodeGList :: Show b => (b -> Text) -> Text -> (a -> [b]) -> a -> Text
encodeGList wa n f x = encodeList wa n (f x)

encodeList :: Show a => (a -> Text) -> Text -> [a] -> Text
encodeList wa n xs =
  [text|
  $n == $sxs
  |]
  where
    sxs = setTla wa xs

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
