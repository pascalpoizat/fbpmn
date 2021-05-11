---------------- MODULE e038TravelAgency ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Customer_" :> { "Ticket", "NoMore", "Offer", "Confirmation" }
  @@ "TravelAgency_" :> { "Abort", "Payment", "Travel" }

ContainRel ==
  "Customer_" :> { "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "EndEvent_0u6deep", "IntermediateThrowEvent_12d113r", "Task_1q91vog", "BoundaryEvent_0qlhw6m", "EndEvent_0syu44v", "IntermediateThrowEvent_02q48nh" }
  @@ "SubProcess_1agd6n3" :> { "StartEvent_0qomvov", "IntermediateThrowEvent_0xjpikb", "IntermediateThrowEvent_0neineb", "Task_002ndsu", "Task_1ne4gpy", "EndEvent_1vkzo14" }
  @@ "TravelAgency_" :> { "StartEvent_1f3jj6d", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q", "ExclusiveGateway_0i09ijx", "SubProcess_1agd6n3", "IntermediateThrowEvent_0b4rm53", "EndEvent_10gqkzy", "BoundaryEvent_19y0yk9", "EndEvent_17rlcaz" }

Node == { "Customer_", "TravelAgency_", "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "EndEvent_0u6deep", "IntermediateThrowEvent_12d113r", "Task_1q91vog", "BoundaryEvent_0qlhw6m", "EndEvent_0syu44v", "IntermediateThrowEvent_02q48nh", "StartEvent_1f3jj6d", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q", "ExclusiveGateway_0i09ijx", "SubProcess_1agd6n3", "IntermediateThrowEvent_0b4rm53", "EndEvent_10gqkzy", "BoundaryEvent_19y0yk9", "EndEvent_17rlcaz", "StartEvent_0qomvov", "IntermediateThrowEvent_0xjpikb", "IntermediateThrowEvent_0neineb", "Task_002ndsu", "Task_1ne4gpy", "EndEvent_1vkzo14" }

Edge == { "MessageFlow_0knd10s", "MessageFlow_1yfhhru", "MessageFlow_1m551dh", "MessageFlow_1goz1mt", "MessageFlow_04an7oz", "MessageFlow_0joml9p", "MessageFlow_18qwt5e", "SequenceFlow_1uwq0b6", "SequenceFlow_0b6ku63", "SequenceFlow_0sfyd5z", "SequenceFlow_016h32p", "SequenceFlow_1rma3l8", "SequenceFlow_1dptcxp", "SequenceFlow_1h5h7h5", "SequenceFlow_0ljbxox", "SequenceFlow_1qku5do", "SequenceFlow_1pk6qce", "SequenceFlow_0ybs6n8", "SequenceFlow_1fn4lqy", "SequenceFlow_0b34324", "SequenceFlow_0mdvaai", "SequenceFlow_13z4ilm", "SequenceFlow_0rfye55", "SequenceFlow_0yhi6sc", "SequenceFlow_1yvkisw", "SequenceFlow_1oyuvjd", "SequenceFlow_17r8ru7", "SequenceFlow_1j6r6o5", "SequenceFlow_0bejayl", "SequenceFlow_0ot5p93", "SequenceFlow_023db5j" }

Message == { "Offer", "Travel", "Confirmation", "Payment", "Ticket", "NoMore", "Abort" }

msgtype ==
   "MessageFlow_0knd10s" :> "Offer"
@@ "MessageFlow_1yfhhru" :> "Travel"
@@ "MessageFlow_1m551dh" :> "Confirmation"
@@ "MessageFlow_1goz1mt" :> "Payment"
@@ "MessageFlow_04an7oz" :> "Ticket"
@@ "MessageFlow_0joml9p" :> "NoMore"
@@ "MessageFlow_18qwt5e" :> "Abort"


source ==
   "MessageFlow_0knd10s" :> "Task_1bn6n5q"
@@ "MessageFlow_1yfhhru" :> "Task_1v9s881"
@@ "MessageFlow_1m551dh" :> "Task_002ndsu"
@@ "MessageFlow_1goz1mt" :> "Task_1q91vog"
@@ "MessageFlow_04an7oz" :> "Task_1ne4gpy"
@@ "MessageFlow_0joml9p" :> "IntermediateThrowEvent_0b4rm53"
@@ "MessageFlow_18qwt5e" :> "IntermediateThrowEvent_02q48nh"
@@ "SequenceFlow_1uwq0b6" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0sfyd5z" :> "Task_07u875a"
@@ "SequenceFlow_016h32p" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1rma3l8" :> "StartEvent_1"
@@ "SequenceFlow_1dptcxp" :> "Task_1v9s881"
@@ "SequenceFlow_1h5h7h5" :> "Task_1q91vog"
@@ "SequenceFlow_0ljbxox" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_1qku5do" :> "EndEvent_0u6deep"
@@ "SequenceFlow_1pk6qce" :> "BoundaryEvent_0qlhw6m"
@@ "SequenceFlow_0ybs6n8" :> "IntermediateThrowEvent_02q48nh"
@@ "SequenceFlow_1fn4lqy" :> "StartEvent_1f3jj6d"
@@ "SequenceFlow_0b34324" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0mdvaai" :> "Task_1bn6n5q"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_0rfye55" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_0yhi6sc" :> "IntermediateThrowEvent_0b4rm53"
@@ "SequenceFlow_1yvkisw" :> "SubProcess_1agd6n3"
@@ "SequenceFlow_1oyuvjd" :> "BoundaryEvent_19y0yk9"
@@ "SequenceFlow_17r8ru7" :> "StartEvent_0qomvov"
@@ "SequenceFlow_1j6r6o5" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_0bejayl" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_0ot5p93" :> "Task_002ndsu"
@@ "SequenceFlow_023db5j" :> "Task_1ne4gpy"

target ==
   "MessageFlow_0knd10s" :> "Task_07u875a"
@@ "MessageFlow_1yfhhru" :> "IntermediateThrowEvent_0xjpikb"
@@ "MessageFlow_1m551dh" :> "EndEvent_0u6deep"
@@ "MessageFlow_1goz1mt" :> "IntermediateThrowEvent_0neineb"
@@ "MessageFlow_04an7oz" :> "IntermediateThrowEvent_12d113r"
@@ "MessageFlow_0joml9p" :> "BoundaryEvent_0qlhw6m"
@@ "MessageFlow_18qwt5e" :> "BoundaryEvent_19y0yk9"
@@ "SequenceFlow_1uwq0b6" :> "Task_1v9s881"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_0sfyd5z" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_016h32p" :> "Task_07u875a"
@@ "SequenceFlow_1rma3l8" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1dptcxp" :> "Task_1q91vog"
@@ "SequenceFlow_1h5h7h5" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_0ljbxox" :> "EndEvent_0u6deep"
@@ "SequenceFlow_1qku5do" :> "EndEvent_055yt9k"
@@ "SequenceFlow_1pk6qce" :> "IntermediateThrowEvent_02q48nh"
@@ "SequenceFlow_0ybs6n8" :> "EndEvent_0syu44v"
@@ "SequenceFlow_1fn4lqy" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0b34324" :> "Task_1bn6n5q"
@@ "SequenceFlow_0mdvaai" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0rfye55" :> "IntermediateThrowEvent_0b4rm53"
@@ "SequenceFlow_0yhi6sc" :> "SubProcess_1agd6n3"
@@ "SequenceFlow_1yvkisw" :> "EndEvent_10gqkzy"
@@ "SequenceFlow_1oyuvjd" :> "EndEvent_17rlcaz"
@@ "SequenceFlow_17r8ru7" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_1j6r6o5" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_0bejayl" :> "Task_002ndsu"
@@ "SequenceFlow_0ot5p93" :> "Task_1ne4gpy"
@@ "SequenceFlow_023db5j" :> "EndEvent_1vkzo14"

CatN ==
   "Customer_" :> Process
@@ "TravelAgency_" :> Process
@@ "Task_1v9s881" :> SendTask
@@ "ExclusiveGateway_192ovii" :> ExclusiveOr
@@ "ExclusiveGateway_0wgdt1i" :> ExclusiveOr
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_07u875a" :> ReceiveTask
@@ "EndEvent_055yt9k" :> NoneEndEvent
@@ "EndEvent_0u6deep" :> CatchMessageIntermediateEvent
@@ "IntermediateThrowEvent_12d113r" :> CatchMessageIntermediateEvent
@@ "Task_1q91vog" :> SendTask
@@ "BoundaryEvent_0qlhw6m" :> MessageBoundaryEvent
@@ "EndEvent_0syu44v" :> NoneEndEvent
@@ "IntermediateThrowEvent_02q48nh" :> ThrowMessageIntermediateEvent
@@ "StartEvent_1f3jj6d" :> NoneStartEvent
@@ "ExclusiveGateway_1dc5v3z" :> ExclusiveOr
@@ "Task_1bn6n5q" :> SendTask
@@ "ExclusiveGateway_0i09ijx" :> ExclusiveOr
@@ "SubProcess_1agd6n3" :> SubProcess
@@ "IntermediateThrowEvent_0b4rm53" :> ThrowMessageIntermediateEvent
@@ "EndEvent_10gqkzy" :> NoneEndEvent
@@ "BoundaryEvent_19y0yk9" :> MessageBoundaryEvent
@@ "EndEvent_17rlcaz" :> NoneEndEvent
@@ "StartEvent_0qomvov" :> NoneStartEvent
@@ "IntermediateThrowEvent_0xjpikb" :> CatchMessageIntermediateEvent
@@ "IntermediateThrowEvent_0neineb" :> CatchMessageIntermediateEvent
@@ "Task_002ndsu" :> SendTask
@@ "Task_1ne4gpy" :> SendTask
@@ "EndEvent_1vkzo14" :> NoneEndEvent

CatE ==
   "MessageFlow_0knd10s" :> MessageFlow
@@ "MessageFlow_1yfhhru" :> MessageFlow
@@ "MessageFlow_1m551dh" :> MessageFlow
@@ "MessageFlow_1goz1mt" :> MessageFlow
@@ "MessageFlow_04an7oz" :> MessageFlow
@@ "MessageFlow_0joml9p" :> MessageFlow
@@ "MessageFlow_18qwt5e" :> MessageFlow
@@ "SequenceFlow_1uwq0b6" :> ConditionalSeqFlow
@@ "SequenceFlow_0b6ku63" :> DefaultSeqFlow
@@ "SequenceFlow_0sfyd5z" :> NormalSeqFlow
@@ "SequenceFlow_016h32p" :> NormalSeqFlow
@@ "SequenceFlow_1rma3l8" :> NormalSeqFlow
@@ "SequenceFlow_1dptcxp" :> NormalSeqFlow
@@ "SequenceFlow_1h5h7h5" :> NormalSeqFlow
@@ "SequenceFlow_0ljbxox" :> NormalSeqFlow
@@ "SequenceFlow_1qku5do" :> NormalSeqFlow
@@ "SequenceFlow_1pk6qce" :> NormalSeqFlow
@@ "SequenceFlow_0ybs6n8" :> NormalSeqFlow
@@ "SequenceFlow_1fn4lqy" :> NormalSeqFlow
@@ "SequenceFlow_0b34324" :> NormalSeqFlow
@@ "SequenceFlow_0mdvaai" :> NormalSeqFlow
@@ "SequenceFlow_13z4ilm" :> ConditionalSeqFlow
@@ "SequenceFlow_0rfye55" :> DefaultSeqFlow
@@ "SequenceFlow_0yhi6sc" :> NormalSeqFlow
@@ "SequenceFlow_1yvkisw" :> NormalSeqFlow
@@ "SequenceFlow_1oyuvjd" :> NormalSeqFlow
@@ "SequenceFlow_17r8ru7" :> NormalSeqFlow
@@ "SequenceFlow_1j6r6o5" :> NormalSeqFlow
@@ "SequenceFlow_0bejayl" :> NormalSeqFlow
@@ "SequenceFlow_0ot5p93" :> NormalSeqFlow
@@ "SequenceFlow_023db5j" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_0qlhw6m" :> [ attachedTo |-> "Task_07u875a", cancelActivity |-> TRUE ]
@@ "BoundaryEvent_19y0yk9" :> [ attachedTo |-> "SubProcess_1agd6n3", cancelActivity |-> TRUE ]

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

