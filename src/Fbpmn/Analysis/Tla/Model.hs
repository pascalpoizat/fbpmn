module Fbpmn.Analysis.Tla.Model where

import Data.Aeson
  ( FromJSON,
    FromJSONKey,
    ToJSON,
    ToJSONKey,
  )
import qualified Data.Map.Strict as M (filter, mapWithKey)
import Fbpmn.Helper (Id)

type Variable = Id
data Status
  = Success
  | Failure
  deriving (Eq, Show, Generic)

instance ToJSON Status

instance FromJSON Status

data Value
  = MapValue (Map Variable Value) -- [ k1 |-> v1, k2 |-> v2, ... ]
  | BagValue (Map Value Value) -- ( v1 :> 1 @@ v2 :> 3 @@ ... )
  | TupleValue [Value] -- << v1, v2, ... >>
  | SetValue [Value] -- { v1, v2, ... }
  | IntegerValue Integer -- 1
  | StringValue String -- "foo"
  | VariableValue Variable -- foo
  deriving (Eq, Ord, Show, Generic)

instance ToJSON Value

instance FromJSON Value

instance ToJSONKey Value

instance FromJSONKey Value

data CounterExampleState = CounterExampleState
  { sid :: Integer,
    sinfo :: String,
    svalue :: Map Variable Value
  }
  deriving (Eq, Show, Generic)

instance ToJSON CounterExampleState

instance FromJSON CounterExampleState

type CounterExample = [CounterExampleState]

data Log = Log
  { lname :: String, -- name of the log
    lmodel :: Maybe String, -- path of the model
    lstatus :: Status, -- status (success/failure)
    lcex :: Maybe CounterExample -- counter example (if failure)
  }
  deriving (Eq, Show, Generic)

instance ToJSON Log

instance FromJSON Log

isValidLog :: Log -> Bool
isValidLog (Log _ _ Success Nothing) = True
isValidLog (Log _ _ Failure (Just _)) = True
isValidLog _ = False

filterLog :: Log -> Log
filterLog (Log n m Failure (Just cx)) =
  Log n m Failure (Just $ filterCounterExample cx)
filterLog m = m

filterCounterExample ::
  CounterExample ->
  CounterExample
filterCounterExample cs = filterState <$> cs

filterState ::
  CounterExampleState ->
  CounterExampleState
filterState (CounterExampleState sid sinfo vs) =
  CounterExampleState sid sinfo (M.mapWithKey f vs)
  where
    f :: (Variable -> Value -> Value)
    f "edgemarks" (MapValue ems) = MapValue $ M.filter keep ems
    f "nodemarks" (MapValue nms) = MapValue $ M.filter keep nms
    f _ x = x
    keep :: Value -> Bool
    keep (IntegerValue n) = n /= 0
    keep _ = True
