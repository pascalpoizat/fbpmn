module Fbpmn.Analysis.Alloy.Model where

data AlloyProperty = Safety | SimpleTermination | CorrectTermination

data AlloyAction = Run | Check

data AlloyVerification = AlloyVerification
  { action   :: AlloyAction
  , property :: AlloyProperty
  , nb       :: Natural
}
