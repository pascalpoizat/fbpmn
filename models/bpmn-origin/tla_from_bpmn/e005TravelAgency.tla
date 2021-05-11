---------------- MODULE e005TravelAgency ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Customer_" :> { "Ticket", "Offer", "Confirmation" }
  @@ "TravelAgency_" :> { "Payment", "Travel" }

ContainRel ==
  "Customer_" :> { "IntermediateThrowEvent_12d113r", "Task_1q91vog", "EndEvent_0u6deep", "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k" }
  @@ "TravelAgency_" :> { "StartEvent_1f3jj6d", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q", "ExclusiveGateway_0i09ijx", "IntermediateThrowEvent_0xjpikb", "Task_1ne4gpy", "EndEvent_10gqkzy", "IntermediateThrowEvent_0neineb", "Task_002ndsu" }

Node == { "Customer_", "TravelAgency_", "IntermediateThrowEvent_12d113r", "Task_1q91vog", "EndEvent_0u6deep", "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "StartEvent_1f3jj6d", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q", "ExclusiveGateway_0i09ijx", "IntermediateThrowEvent_0xjpikb", "Task_1ne4gpy", "EndEvent_10gqkzy", "IntermediateThrowEvent_0neineb", "Task_002ndsu" }

Edge == { "MessageFlow_0knd10s", "MessageFlow_1yfhhru", "MessageFlow_1m551dh", "MessageFlow_1goz1mt", "MessageFlow_04an7oz", "SequenceFlow_1h086yg", "SequenceFlow_00r0rkx", "SequenceFlow_03104wi", "SequenceFlow_0bgaa0c", "SequenceFlow_1uwq0b6", "SequenceFlow_0b6ku63", "SequenceFlow_0sfyd5z", "SequenceFlow_016h32p", "SequenceFlow_1rma3l8", "SequenceFlow_1fn4lqy", "SequenceFlow_0b34324", "SequenceFlow_0mdvaai", "SequenceFlow_13z4ilm", "SequenceFlow_0rfye55", "SequenceFlow_0bztvlk", "SequenceFlow_1d2k55z", "SequenceFlow_09i1nd5", "SequenceFlow_05p1rba" }

Message == { "Offer", "Travel", "Confirmation", "Payment", "Ticket" }

msgtype ==
   "MessageFlow_0knd10s" :> "Offer"
@@ "MessageFlow_1yfhhru" :> "Travel"
@@ "MessageFlow_1m551dh" :> "Confirmation"
@@ "MessageFlow_1goz1mt" :> "Payment"
@@ "MessageFlow_04an7oz" :> "Ticket"


source ==
   "MessageFlow_0knd10s" :> "Task_1bn6n5q"
@@ "MessageFlow_1yfhhru" :> "Task_1v9s881"
@@ "MessageFlow_1m551dh" :> "Task_002ndsu"
@@ "MessageFlow_1goz1mt" :> "Task_1q91vog"
@@ "MessageFlow_04an7oz" :> "Task_1ne4gpy"
@@ "SequenceFlow_1h086yg" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_00r0rkx" :> "Task_1q91vog"
@@ "SequenceFlow_03104wi" :> "EndEvent_0u6deep"
@@ "SequenceFlow_0bgaa0c" :> "Task_1v9s881"
@@ "SequenceFlow_1uwq0b6" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0sfyd5z" :> "Task_07u875a"
@@ "SequenceFlow_016h32p" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1rma3l8" :> "StartEvent_1"
@@ "SequenceFlow_1fn4lqy" :> "StartEvent_1f3jj6d"
@@ "SequenceFlow_0b34324" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0mdvaai" :> "Task_1bn6n5q"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_0rfye55" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_0bztvlk" :> "Task_1ne4gpy"
@@ "SequenceFlow_1d2k55z" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_09i1nd5" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_05p1rba" :> "Task_002ndsu"

target ==
   "MessageFlow_0knd10s" :> "Task_07u875a"
@@ "MessageFlow_1yfhhru" :> "IntermediateThrowEvent_0xjpikb"
@@ "MessageFlow_1m551dh" :> "EndEvent_0u6deep"
@@ "MessageFlow_1goz1mt" :> "IntermediateThrowEvent_0neineb"
@@ "MessageFlow_04an7oz" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_1h086yg" :> "EndEvent_055yt9k"
@@ "SequenceFlow_00r0rkx" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_03104wi" :> "Task_1q91vog"
@@ "SequenceFlow_0bgaa0c" :> "EndEvent_0u6deep"
@@ "SequenceFlow_1uwq0b6" :> "Task_1v9s881"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_0sfyd5z" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_016h32p" :> "Task_07u875a"
@@ "SequenceFlow_1rma3l8" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1fn4lqy" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0b34324" :> "Task_1bn6n5q"
@@ "SequenceFlow_0mdvaai" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0rfye55" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_0bztvlk" :> "EndEvent_10gqkzy"
@@ "SequenceFlow_1d2k55z" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_09i1nd5" :> "Task_002ndsu"
@@ "SequenceFlow_05p1rba" :> "Task_1ne4gpy"

CatN ==
   "Customer_" :> Process
@@ "TravelAgency_" :> Process
@@ "IntermediateThrowEvent_12d113r" :> CatchMessageIntermediateEvent
@@ "Task_1q91vog" :> SendTask
@@ "EndEvent_0u6deep" :> CatchMessageIntermediateEvent
@@ "Task_1v9s881" :> SendTask
@@ "ExclusiveGateway_192ovii" :> ExclusiveOr
@@ "ExclusiveGateway_0wgdt1i" :> ExclusiveOr
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_07u875a" :> ReceiveTask
@@ "EndEvent_055yt9k" :> NoneEndEvent
@@ "StartEvent_1f3jj6d" :> NoneStartEvent
@@ "ExclusiveGateway_1dc5v3z" :> ExclusiveOr
@@ "Task_1bn6n5q" :> SendTask
@@ "ExclusiveGateway_0i09ijx" :> Parallel
@@ "IntermediateThrowEvent_0xjpikb" :> CatchMessageIntermediateEvent
@@ "Task_1ne4gpy" :> SendTask
@@ "EndEvent_10gqkzy" :> TerminateEndEvent
@@ "IntermediateThrowEvent_0neineb" :> CatchMessageIntermediateEvent
@@ "Task_002ndsu" :> SendTask

CatE ==
   "MessageFlow_0knd10s" :> MessageFlow
@@ "MessageFlow_1yfhhru" :> MessageFlow
@@ "MessageFlow_1m551dh" :> MessageFlow
@@ "MessageFlow_1goz1mt" :> MessageFlow
@@ "MessageFlow_04an7oz" :> MessageFlow
@@ "SequenceFlow_1h086yg" :> NormalSeqFlow
@@ "SequenceFlow_00r0rkx" :> NormalSeqFlow
@@ "SequenceFlow_03104wi" :> NormalSeqFlow
@@ "SequenceFlow_0bgaa0c" :> NormalSeqFlow
@@ "SequenceFlow_1uwq0b6" :> NormalSeqFlow
@@ "SequenceFlow_0b6ku63" :> NormalSeqFlow
@@ "SequenceFlow_0sfyd5z" :> NormalSeqFlow
@@ "SequenceFlow_016h32p" :> NormalSeqFlow
@@ "SequenceFlow_1rma3l8" :> NormalSeqFlow
@@ "SequenceFlow_1fn4lqy" :> NormalSeqFlow
@@ "SequenceFlow_0b34324" :> NormalSeqFlow
@@ "SequenceFlow_0mdvaai" :> NormalSeqFlow
@@ "SequenceFlow_13z4ilm" :> NormalSeqFlow
@@ "SequenceFlow_0rfye55" :> NormalSeqFlow
@@ "SequenceFlow_0bztvlk" :> NormalSeqFlow
@@ "SequenceFlow_1d2k55z" :> NormalSeqFlow
@@ "SequenceFlow_09i1nd5" :> NormalSeqFlow
@@ "SequenceFlow_05p1rba" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
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

