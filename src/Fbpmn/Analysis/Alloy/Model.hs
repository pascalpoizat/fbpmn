module Fbpmn.Analysis.Alloy.Model where

import Relude (Natural)

data AlloyProperty = Safety | SimpleTermination | CorrectTermination

data AlloyAction = Run | Check

data AlloyVerification = AlloyVerification
  { action :: AlloyAction,
    property :: AlloyProperty,
    nb :: Natural
  }
