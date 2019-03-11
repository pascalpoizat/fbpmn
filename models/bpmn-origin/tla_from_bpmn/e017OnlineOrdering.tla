---------------- MODULE e017OnlineOrdering ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_Id" :> { "exclusivegateway4", "exclusivegateway3", "validatePayment", "inclusivegateway2", "payOnDelivery", "card", "giftVoucher", "inclusivegateway1", "Payment", "selectItems", "exclusivegateway2", "signUp", "signIn", "exclusivegateway1", "startevent1", "initiateShipping", "parallelgateway1", "packageItems", "parallelgateway2", "initiateDelivery", "email", "notifyUser", "sms", "transport", "parallelgateway5", "parallelgateway6", "parallelgateway3", "parallelgateway4", "endevent1", "generateTrackingInfo", "errorendevent1" }

Node == {
  "Process_Id","exclusivegateway4","exclusivegateway3","validatePayment","inclusivegateway2","payOnDelivery","card","giftVoucher","inclusivegateway1","Payment","selectItems","exclusivegateway2","signUp","signIn","exclusivegateway1","startevent1","initiateShipping","parallelgateway1","packageItems","parallelgateway2","initiateDelivery","email","notifyUser","sms","transport","parallelgateway5","parallelgateway6","parallelgateway3","parallelgateway4","endevent1","generateTrackingInfo","errorendevent1"
}

Edge == {
  "flow3","flow4","flow5","flow6","flow7","flow8","flow9","flow10","flow11","flow12","flow13","flow14","flow15","flow16","flow17","flow19","flow20","flow21","flow30","flow35","flow39","flow62","flow31","flow32","flow33","flow34","flow57","flow59","flow41","flow43","flow56","flow58","flow60","flow47","flow61","flow63"
}

Message == {  }

msgtype ==
    [ i \in {} |-> {}]

source ==
   "flow3" :> "exclusivegateway1"
@@ "flow4" :> "exclusivegateway1"
@@ "flow5" :> "signUp"
@@ "flow6" :> "signIn"
@@ "flow7" :> "startevent1"
@@ "flow8" :> "selectItems"
@@ "flow9" :> "exclusivegateway2"
@@ "flow10" :> "Payment"
@@ "flow11" :> "inclusivegateway1"
@@ "flow12" :> "inclusivegateway1"
@@ "flow13" :> "inclusivegateway1"
@@ "flow14" :> "giftVoucher"
@@ "flow15" :> "card"
@@ "flow16" :> "inclusivegateway2"
@@ "flow17" :> "validatePayment"
@@ "flow19" :> "exclusivegateway3"
@@ "flow20" :> "exclusivegateway3"
@@ "flow21" :> "payOnDelivery"
@@ "flow30" :> "initiateShipping"
@@ "flow35" :> "parallelgateway2"
@@ "flow39" :> "initiateDelivery"
@@ "flow62" :> "exclusivegateway4"
@@ "flow31" :> "parallelgateway1"
@@ "flow32" :> "parallelgateway1"
@@ "flow33" :> "generateTrackingInfo"
@@ "flow34" :> "packageItems"
@@ "flow57" :> "parallelgateway5"
@@ "flow59" :> "email"
@@ "flow41" :> "parallelgateway3"
@@ "flow43" :> "parallelgateway3"
@@ "flow56" :> "notifyUser"
@@ "flow58" :> "parallelgateway5"
@@ "flow60" :> "sms"
@@ "flow47" :> "transport"
@@ "flow61" :> "parallelgateway6"
@@ "flow63" :> "parallelgateway4"

target ==
   "flow3" :> "signIn"
@@ "flow4" :> "signUp"
@@ "flow5" :> "exclusivegateway2"
@@ "flow6" :> "exclusivegateway2"
@@ "flow7" :> "selectItems"
@@ "flow8" :> "exclusivegateway1"
@@ "flow9" :> "Payment"
@@ "flow10" :> "inclusivegateway1"
@@ "flow11" :> "giftVoucher"
@@ "flow12" :> "card"
@@ "flow13" :> "payOnDelivery"
@@ "flow14" :> "inclusivegateway2"
@@ "flow15" :> "inclusivegateway2"
@@ "flow16" :> "validatePayment"
@@ "flow17" :> "exclusivegateway3"
@@ "flow19" :> "exclusivegateway4"
@@ "flow20" :> "errorendevent1"
@@ "flow21" :> "exclusivegateway4"
@@ "flow30" :> "parallelgateway1"
@@ "flow35" :> "initiateDelivery"
@@ "flow39" :> "parallelgateway3"
@@ "flow62" :> "initiateShipping"
@@ "flow31" :> "packageItems"
@@ "flow32" :> "generateTrackingInfo"
@@ "flow33" :> "parallelgateway2"
@@ "flow34" :> "parallelgateway2"
@@ "flow57" :> "email"
@@ "flow59" :> "parallelgateway6"
@@ "flow41" :> "notifyUser"
@@ "flow43" :> "transport"
@@ "flow56" :> "parallelgateway5"
@@ "flow58" :> "sms"
@@ "flow60" :> "parallelgateway6"
@@ "flow47" :> "parallelgateway4"
@@ "flow61" :> "parallelgateway4"
@@ "flow63" :> "endevent1"

CatN ==
   "Process_Id" :> Process
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
   "flow3" :> ConditionalSeqFlow
@@ "flow4" :> DefaultSeqFlow
@@ "flow5" :> NormalSeqFlow
@@ "flow6" :> NormalSeqFlow
@@ "flow7" :> NormalSeqFlow
@@ "flow8" :> NormalSeqFlow
@@ "flow9" :> NormalSeqFlow
@@ "flow10" :> NormalSeqFlow
@@ "flow11" :> ConditionalSeqFlow
@@ "flow12" :> ConditionalSeqFlow
@@ "flow13" :> DefaultSeqFlow
@@ "flow14" :> NormalSeqFlow
@@ "flow15" :> NormalSeqFlow
@@ "flow16" :> NormalSeqFlow
@@ "flow17" :> NormalSeqFlow
@@ "flow19" :> DefaultSeqFlow
@@ "flow20" :> ConditionalSeqFlow
@@ "flow21" :> NormalSeqFlow
@@ "flow30" :> NormalSeqFlow
@@ "flow35" :> NormalSeqFlow
@@ "flow39" :> NormalSeqFlow
@@ "flow62" :> NormalSeqFlow
@@ "flow31" :> NormalSeqFlow
@@ "flow32" :> NormalSeqFlow
@@ "flow33" :> NormalSeqFlow
@@ "flow34" :> NormalSeqFlow
@@ "flow57" :> NormalSeqFlow
@@ "flow59" :> NormalSeqFlow
@@ "flow41" :> NormalSeqFlow
@@ "flow43" :> NormalSeqFlow
@@ "flow56" :> NormalSeqFlow
@@ "flow58" :> NormalSeqFlow
@@ "flow60" :> NormalSeqFlow
@@ "flow47" :> NormalSeqFlow
@@ "flow61" :> NormalSeqFlow
@@ "flow63" :> NormalSeqFlow

LOCAL preEdges ==
<<"inclusivegateway2", "flow14">> :> {"flow10", "flow11", "flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
@@ <<"inclusivegateway2", "flow15">> :> {"flow10", "flow12", "flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
@@ <<"inclusivegateway1", "flow10">> :> {"flow3", "flow4", "flow5", "flow6", "flow7", "flow8", "flow9"}
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

