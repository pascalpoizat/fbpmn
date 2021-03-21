-- ORMULU align "="
-- ORMULU align "::"

module Fbpmn.BpmnGraph.SpaceModel where

import Data.Map as M (elems, keys)
import Data.Set as S (elems, empty, insert)
import Fbpmn.BpmnGraph.Model (BpmnGraph, Edge, Node, isValidGraph)
import Fbpmn.Helper (Id, allDifferent, allIn', disjoint')

-- | Base Locations
type BaseLocation = Id

-- | Group Locations
type GroupLocation = Id

-- | Space Edges
type SEdge = Id

-- | Variables
type Variable = Id

-- | Space Structure
data SpaceStructure = SpaceStructure
  { -- | base locations
    baseLocations :: [BaseLocation],
    -- | group locations
    groupLocations :: [GroupLocation],
    -- | edges for possible moves between (base) locations
    sEdges :: [SEdge],
    -- | sources of edges
    sSourceE :: Map SEdge BaseLocation,
    -- | targets of edges
    sTargetE :: Map SEdge BaseLocation
  }
  deriving (Show)

-- | Space Formula
data SpaceFormula
  = SFTrue
  | SFVar Variable
  | SFBase BaseLocation
  | SFGroup GroupLocation
  | SFNot SpaceFormula
  | SFOr SpaceFormula SpaceFormula
  | SFAnd SpaceFormula SpaceFormula
  | SFReach
  deriving (Show)

fVariables :: SpaceFormula -> [Variable]
fVariables = S.elems . f' S.empty
  where
    f' :: Set Variable -> SpaceFormula -> Set Variable
    f' vs SFTrue = vs
    f' vs (SFVar v) = insert v vs
    f' vs (SFBase _) = vs
    f' vs (SFGroup _) = vs
    f' vs (SFNot f) = f' vs f
    f' vs (SFOr f1 f2) = f' (f' vs f1) f2
    f' vs (SFAnd f1 f2) = f' (f' vs f1) f2
    f' vs SFReach = vs

fBaseLocations :: SpaceFormula -> [BaseLocation]
fBaseLocations = S.elems . f' S.empty
  where
    f' :: Set BaseLocation -> SpaceFormula -> Set BaseLocation
    f' vs SFTrue = vs
    f' vs (SFVar _) = vs
    f' vs (SFBase b) = insert b vs
    f' vs (SFGroup _) = vs
    f' vs (SFNot f) = f' vs f
    f' vs (SFOr f1 f2) = f' (f' vs f1) f2
    f' vs (SFAnd f1 f2) = f' (f' vs f1) f2
    f' vs SFReach = vs

fGroupLocations :: SpaceFormula -> [GroupLocation]
fGroupLocations = S.elems . f' S.empty
  where
    f' :: Set GroupLocation -> SpaceFormula -> Set GroupLocation
    f' vs SFTrue = vs
    f' vs (SFVar _) = vs
    f' vs (SFBase _) = vs
    f' vs (SFGroup g) = insert g vs
    f' vs (SFNot f) = f' vs f
    f' vs (SFOr f1 f2) = f' (f' vs f1) f2
    f' vs (SFAnd f1 f2) = f' (f' vs f1) f2
    f' vs SFReach = vs

-- | Space Actions
data SpaceAction
  = SAPass
  | SAMove SpaceFormula
  | SAUpdate Variable [GroupLocation] [GroupLocation]
  deriving (Show)

-- | Space BPMN Graph
data SpaceBpmnGraph = SpaceBPMNGraph
  { -- | base BPMN Graph
    graph :: BpmnGraph,
    -- | space structure
    spacestructure :: SpaceStructure,
    -- | variables
    variables :: [Variable],
    -- | variables on conditional edges (vs in v : F)
    cVariables :: Map Edge Variable,
    -- | formulas on conditional edges (Fs in v : F)
    cFormulas :: Map Edge SpaceFormula,
    -- | ordering of edges for XOR gateways
    cOrdering :: Map Node [Edge],
    -- | actions associated to tasks
    actions :: Map Node SpaceAction,
    -- | initial configuration parameters
    init :: SpaceConfiguration
  }
  deriving (Show)

-- | Initial Configuration Parameters
data SpaceConfiguration = SpaceConfiguration
  { initialLocations :: Map Node BaseLocation,
    initialSpace :: Map GroupLocation [BaseLocation]
  }
  deriving (Show)

-- | Checks is a space BPMN graph is valid
--  - the underlying BPMN graph is valid
--  - the space structure is valid
--  - conditional edges are valid (variables, local and group locations)
--  - TODO: edges (all but default) outgoing from a XOR gateway are ordered
--  - TODO: actions are valid
--  Note : validations could be done in the transformer or in the target framework (TLA, ...)
isValidSGraph :: SpaceBpmnGraph -> Bool
isValidSGraph g =
  and $
    [ isValidGraph . graph, -- the BPMN graph is valid
      isValidSpaceStructure . spacestructure, -- the space structure is valid
      hasValidCVariables, -- variables used in conditional edges are valid
      hasValidCFormulas -- formulas used in conditional edges are valid
    ]
      <*> [g]

hasValidCFormulas :: SpaceBpmnGraph -> Bool
hasValidCFormulas g =
  all
    ( \x ->
        and $
          [ hasValidFVariables . variables,
            hasValidBLocations . baseLocations . spacestructure,
            hasValidGLocations . groupLocations . spacestructure
          ]
            <*> [g]
            <*> [x]
    )
    $ M.elems . cFormulas $ g

hasValidFVariables :: [Variable] -> SpaceFormula -> Bool
hasValidFVariables vs = all (`elem` vs) . fVariables

hasValidBLocations :: [BaseLocation] -> SpaceFormula -> Bool
hasValidBLocations vs = all (`elem` vs) . fBaseLocations

hasValidGLocations :: [GroupLocation] -> SpaceFormula -> Bool
hasValidGLocations vs = all (`elem` vs) . fGroupLocations

hasValidCVariables :: SpaceBpmnGraph -> Bool
hasValidCVariables g = all (`elem` variables g) $ M.elems . cVariables $ g

-- | Checks if a space structure is valid
isValidSpaceStructure :: SpaceStructure -> Bool
isValidSpaceStructure s =
  and $
    [ allDifferent . baseLocations, -- no duplicate base locations
      allDifferent . groupLocations, -- no duplicate group locations
      baseLocations `disjoint'` groupLocations, -- base and group locations are disjoint
      sEdges `allIn'` (M.keys . sSourceE), -- all move edges have a source
      sEdges `allIn'` (M.keys . sTargetE), -- all move edges have a target
      (M.elems . sSourceE) `allIn'` baseLocations, -- sources of edges are baseLocations
      (M.elems . sTargetE) `allIn'` baseLocations -- targets of edges are baseLocations
    ]
      <*> [s]
