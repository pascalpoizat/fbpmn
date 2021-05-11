---------------- MODULE e017OnlineOrdering ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_" :> {  }

ContainRel ==
  "Process_" :> { "exclusivegateway4", "exclusivegateway3", "validatePayment", "inclusivegateway2", "payOnDelivery", "card", "giftVoucher", "inclusivegateway1", "Payment", "selectItems", "exclusivegateway2", "signUp", "signIn", "exclusivegateway1", "startevent1", "initiateShipping", "parallelgateway1", "packageItems", "parallelgateway2", "initiateDelivery", "email", "notifyUser", "sms", "transport", "parallelgateway5", "parallelgateway6", "parallelgateway3", "parallelgateway4", "endevent1", "generateTrackingInfo", "errorendevent1" }

Node == { "Process_", "exclusivegateway4", "exclusivegateway3", "validatePayment", "inclusivegateway2", "payOnDelivery", "card", "giftVoucher", "inclusivegateway1", "Payment", "selectItems", "exclusivegateway2", "signUp", "signIn", "exclusivegateway1", "startevent1", "initiateShipping", "parallelgateway1", "packageItems", "parallelgateway2", "initiateDelivery", "email", "notifyUser", "sms", "transport", "parallelgateway5", "parallelgateway6", "parallelgateway3", "parallelgateway4", "endevent1", "generateTrackingInfo", "errorendevent1" }

Edge == { "flow63", "flow61", "flow47", "flow60", "flow58", "flow56", "flow43", "flow41", "flow59", "flow57", "flow34", "flow33", "flow32", "flow31", "flow62", "flow39", "flow35", "flow30", "flow21", "flow20", "flow19", "flow17", "flow16", "flow15", "flow14", "flow13", "flow12", "flow11", "flow10", "flow9", "flow8", "flow7", "flow6", "flow5", "flow4", "flow3" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "flow63" :> "parallelgateway4"
@@ "flow61" :> "parallelgateway6"
@@ "flow47" :> "transport"
@@ "flow60" :> "sms"
@@ "flow58" :> "parallelgateway5"
@@ "flow56" :> "notifyUser"
@@ "flow43" :> "parallelgateway3"
@@ "flow41" :> "parallelgateway3"
@@ "flow59" :> "email"
@@ "flow57" :> "parallelgateway5"
@@ "flow34" :> "packageItems"
@@ "flow33" :> "generateTrackingInfo"
@@ "flow32" :> "parallelgateway1"
@@ "flow31" :> "parallelgateway1"
@@ "flow62" :> "exclusivegateway4"
@@ "flow39" :> "initiateDelivery"
@@ "flow35" :> "parallelgateway2"
@@ "flow30" :> "initiateShipping"
@@ "flow21" :> "payOnDelivery"
@@ "flow20" :> "exclusivegateway3"
@@ "flow19" :> "exclusivegateway3"
@@ "flow17" :> "validatePayment"
@@ "flow16" :> "inclusivegateway2"
@@ "flow15" :> "card"
@@ "flow14" :> "giftVoucher"
@@ "flow13" :> "inclusivegateway1"
@@ "flow12" :> "inclusivegateway1"
@@ "flow11" :> "inclusivegateway1"
@@ "flow10" :> "Payment"
@@ "flow9" :> "exclusivegateway2"
@@ "flow8" :> "selectItems"
@@ "flow7" :> "startevent1"
@@ "flow6" :> "signIn"
@@ "flow5" :> "signUp"
@@ "flow4" :> "exclusivegateway1"
@@ "flow3" :> "exclusivegateway1"

target ==
   "flow63" :> "endevent1"
@@ "flow61" :> "parallelgateway4"
@@ "flow47" :> "parallelgateway4"
@@ "flow60" :> "parallelgateway6"
@@ "flow58" :> "sms"
@@ "flow56" :> "parallelgateway5"
@@ "flow43" :> "transport"
@@ "flow41" :> "notifyUser"
@@ "flow59" :> "parallelgateway6"
@@ "flow57" :> "email"
@@ "flow34" :> "parallelgateway2"
@@ "flow33" :> "parallelgateway2"
@@ "flow32" :> "generateTrackingInfo"
@@ "flow31" :> "packageItems"
@@ "flow62" :> "initiateShipping"
@@ "flow39" :> "parallelgateway3"
@@ "flow35" :> "initiateDelivery"
@@ "flow30" :> "parallelgateway1"
@@ "flow21" :> "exclusivegateway4"
@@ "flow20" :> "errorendevent1"
@@ "flow19" :> "exclusivegateway4"
@@ "flow17" :> "exclusivegateway3"
@@ "flow16" :> "validatePayment"
@@ "flow15" :> "inclusivegateway2"
@@ "flow14" :> "inclusivegateway2"
@@ "flow13" :> "payOnDelivery"
@@ "flow12" :> "card"
@@ "flow11" :> "giftVoucher"
@@ "flow10" :> "inclusivegateway1"
@@ "flow9" :> "Payment"
@@ "flow8" :> "exclusivegateway1"
@@ "flow7" :> "selectItems"
@@ "flow6" :> "exclusivegateway2"
@@ "flow5" :> "exclusivegateway2"
@@ "flow4" :> "signUp"
@@ "flow3" :> "signIn"

CatN ==
   "Process_" :> Process
@@ "exclusivegateway4" :> ExclusiveOr
@@ "exclusivegateway3" :> ExclusiveOr
@@ "validatePayment" :> AbstractTask
@@ "inclusivegateway2" :> InclusiveOr
@@ "payOnDelivery" :> AbstractTask
@@ "card" :> AbstractTask
@@ "giftVoucher" :> AbstractTask
@@ "inclusivegateway1" :> InclusiveOr
@@ "Payment" :> AbstractTask
@@ "selectItems" :> AbstractTask
@@ "exclusivegateway2" :> ExclusiveOr
@@ "signUp" :> AbstractTask
@@ "signIn" :> AbstractTask
@@ "exclusivegateway1" :> ExclusiveOr
@@ "startevent1" :> NoneStartEvent
@@ "initiateShipping" :> AbstractTask
@@ "parallelgateway1" :> Parallel
@@ "packageItems" :> AbstractTask
@@ "parallelgateway2" :> Parallel
@@ "initiateDelivery" :> AbstractTask
@@ "email" :> AbstractTask
@@ "notifyUser" :> AbstractTask
@@ "sms" :> AbstractTask
@@ "transport" :> AbstractTask
@@ "parallelgateway5" :> Parallel
@@ "parallelgateway6" :> Parallel
@@ "parallelgateway3" :> Parallel
@@ "parallelgateway4" :> Parallel
@@ "endevent1" :> NoneEndEvent
@@ "generateTrackingInfo" :> AbstractTask
@@ "errorendevent1" :> NoneEndEvent

CatE ==
   "flow63" :> NormalSeqFlow
@@ "flow61" :> NormalSeqFlow
@@ "flow47" :> NormalSeqFlow
@@ "flow60" :> NormalSeqFlow
@@ "flow58" :> NormalSeqFlow
@@ "flow56" :> NormalSeqFlow
@@ "flow43" :> NormalSeqFlow
@@ "flow41" :> NormalSeqFlow
@@ "flow59" :> NormalSeqFlow
@@ "flow57" :> NormalSeqFlow
@@ "flow34" :> NormalSeqFlow
@@ "flow33" :> NormalSeqFlow
@@ "flow32" :> NormalSeqFlow
@@ "flow31" :> NormalSeqFlow
@@ "flow62" :> NormalSeqFlow
@@ "flow39" :> NormalSeqFlow
@@ "flow35" :> NormalSeqFlow
@@ "flow30" :> NormalSeqFlow
@@ "flow21" :> NormalSeqFlow
@@ "flow20" :> ConditionalSeqFlow
@@ "flow19" :> DefaultSeqFlow
@@ "flow17" :> NormalSeqFlow
@@ "flow16" :> NormalSeqFlow
@@ "flow15" :> NormalSeqFlow
@@ "flow14" :> NormalSeqFlow
@@ "flow13" :> DefaultSeqFlow
@@ "flow12" :> ConditionalSeqFlow
@@ "flow11" :> ConditionalSeqFlow
@@ "flow10" :> NormalSeqFlow
@@ "flow9" :> NormalSeqFlow
@@ "flow8" :> NormalSeqFlow
@@ "flow7" :> NormalSeqFlow
@@ "flow6" :> NormalSeqFlow
@@ "flow5" :> NormalSeqFlow
@@ "flow4" :> DefaultSeqFlow
@@ "flow3" :> ConditionalSeqFlow

LOCAL preEdges ==
   <<"inclusivegateway2", "flow15">> :> {"flow10", "flow12", "flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
@@ <<"inclusivegateway2", "flow14">> :> {"flow10", "flow11", "flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
@@ <<"inclusivegateway1", "flow10">> :> {"flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
  [ i \in {} |-> {}]

WF == INSTANCE PWSWellFormed
ASSUME WF!WellTyped
ASSUME WF!WellFormedness

ConstraintNode == TRUE \* none
ConstraintEdge == TRUE \* none
Constraint == TRUE     \* none
INSTANCE PWSConstraints
INSTANCE UserProperties
INSTANCE PWSSemantics

================================================================

