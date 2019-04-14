module Fbpmn.Analysis.Tla.Model where

import           Data.Aeson                     ( FromJSON
                                                , ToJSON
                                                , FromJSONKey
                                                , ToJSONKey
                                                )
import qualified Data.Map.Strict               as M
                                                ( Map
                                                , filterWithKey
                                                )

data Status
  = Success
  | Failure
  deriving (Eq, Show, Generic)

instance ToJSON Status

instance FromJSON Status

type Variable = String

data Value =
    MapValue (Map Variable Value) -- [ k1 |-> v1, k2 |-> v2, ... ]
  | BagValue (Map Value Integer)  -- ( v1 :> 1, v2 :> 3, ... )
  | TupleValue [Value]            -- << v1, v2, ... >>
  | IntegerValue Integer          -- 1
  | StringValue String            -- "foo"
  | VariableValue Variable        -- foo
  deriving (Eq, Ord, Show, Generic)

instance ToJSON Value

instance FromJSON Value

instance ToJSONKey Value

instance FromJSONKey Value

data CounterExampleState = CounterExampleState
  { sid :: Integer
  , svalue :: M.Map Variable Value
  } deriving (Eq, Show, Generic)

instance ToJSON CounterExampleState

instance FromJSON CounterExampleState

type CounterExample = [CounterExampleState]

data Log =
  Log Status
      (Maybe CounterExample)
  deriving (Eq, Show, Generic)

instance ToJSON Log

instance FromJSON Log

isValidLog :: Log -> Bool
isValidLog (Log Success Nothing ) = True
isValidLog (Log Failure (Just _)) = True
isValidLog _                      = False

hasToken :: Variable -> Integer -> Bool
hasToken _ v = v /= 0

filterCounterExample :: (Variable -> Value -> Bool)
                     -> CounterExample
                     -> CounterExample
filterCounterExample f cs = filterStateValue f <$> cs

filterStateValue :: (Variable -> Value -> Bool)
                 -> CounterExampleState
                 -> CounterExampleState
filterStateValue f (CounterExampleState sid vs) =
  CounterExampleState sid $ M.filterWithKey f vs

