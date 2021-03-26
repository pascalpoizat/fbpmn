-- ORMULU align "="
-- ORMULU align "::"

module Fbpmn.BpmnGraph.SpaceModel where

import Data.Map as M (elems, keys, empty)
import Data.Set as S (elems, empty, insert)
import Fbpmn.BpmnGraph.Model (BpmnGraph, Edge, Node, isValidGraph)
import Fbpmn.Helper (Id, allDifferent, allIn', disjoint')
import Relude.Extra.Lens (Lens', lens)

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

instance Semigroup SpaceStructure where
  (SpaceStructure bs gs se sse ste) <> (SpaceStructure bs' gs' se' sse' ste') =
    SpaceStructure
      (bs <> bs')
      (gs <> gs')
      (se <> se')
      (sse <> sse')
      (ste <> ste')

instance Monoid SpaceStructure where
  mempty =
    SpaceStructure
      []
      []
      []
      M.empty
      M.empty
      
-- | Kind for Space Formulas
data FormulaKind = SFAll | SFAny
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
data SpaceBpmnGraph = SpaceBpmnGraph
  { -- | base BPMN Graph
    graph :: BpmnGraph,
    -- | space structure
    spacestructure :: SpaceStructure,
    -- | variables
    variables :: [Variable],
    -- | variables on conditional edges (vs in v : k F)
    cVariables :: Map Edge Variable,
    -- | kinds on conditional edges (ks in v : k F)
    cKinds :: Map Edge FormulaKind,
    -- | formulas on conditional edges (Fs in v : k F)
    cFormulas :: Map Edge SpaceFormula,
    -- | ordering of edges for XOR gateways
    cOrdering :: Map Node [Edge],
    -- | actions associated to tasks
    actions :: Map Node SpaceAction,
    -- | initial configuration parameters
    initial :: SpaceConfiguration
  }
  deriving (Show)

instance Semigroup SpaceBpmnGraph where
  (SpaceBpmnGraph g ss vs cvs cks cfs co as i) <> (SpaceBpmnGraph g' ss' vs' cvs' cks' cfs' co' as' i') =
    SpaceBpmnGraph
      (g <> g')
      (ss <> ss')
      (vs <> vs')
      (cvs <> cvs')
      (cks <> cks')
      (cfs <> cfs')
      (co <> co')
      (as <> as')
      (i <> i')

instance Monoid SpaceBpmnGraph where
  mempty =
    SpaceBpmnGraph
      mempty
      mempty
      []
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      mempty

variablesL :: Lens' SpaceBpmnGraph [Variable]
variablesL = lens getter setter
  where
    getter = variables
    setter spaceGraph newVariables = spaceGraph {variables = newVariables}

initialL :: Lens' SpaceBpmnGraph SpaceConfiguration
initialL = lens getter setter
  where
    getter = initial
    setter spaceGraph newInitial = spaceGraph {initial = newInitial}

-- | Initial Configuration Parameters
data SpaceConfiguration = SpaceConfiguration
  { initialLocations :: Map Node BaseLocation,
    initialSpace :: Map GroupLocation [BaseLocation]
  }
  deriving (Show)

instance Semigroup SpaceConfiguration where
  (SpaceConfiguration ils iss) <> (SpaceConfiguration ils' iss') =
    SpaceConfiguration
      (ils <> ils')
      (iss <> iss')

instance Monoid SpaceConfiguration where
  mempty =
    SpaceConfiguration
      M.empty
      M.empty

initialLocationsL :: Lens' SpaceConfiguration (Map Node BaseLocation)
initialLocationsL = lens getter setter
  where
    getter = initialLocations
    setter spaceConfiguration newInitialLocations = spaceConfiguration {initialLocations = newInitialLocations}

-- | Checks is a space BPMN graph is valid
--  - the underlying BPMN graph is valid
--  - the space structure is valid
--  - variables in conditional edges are valid
--  - formulas in conditional edges are valid
--  - TODO: the domain of cVariables is the graph conditional edges (same with cKinds and cFormulas)
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

-- | Checks if formulas on conditional edges are valid
-- - variables are in the graph variables
-- - base locations are in the space structure base locations
-- - group locations are in the space structure group locationss 
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
