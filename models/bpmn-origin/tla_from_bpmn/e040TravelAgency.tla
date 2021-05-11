---------------- MODULE e040TravelAgency ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Customer_" :> { "NoMore", "Ticket", "Offer", "Confirmation" }
  @@ "TravelAgency_" :> { "Abort", "Payment", "Travel" }

ContainRel ==
  "Activity_0re3cuj" :> { "Event_0e98cce", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q" }
  @@ "Customer_" :> { "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "EndEvent_0u6deep", "IntermediateThrowEvent_12d113r", "Task_1q91vog", "BoundaryEvent_0qlhw6m", "EndEvent_0syu44v", "IntermediateThrowEvent_02q48nh" }
  @@ "SubProcess_1agd6n3" :> { "StartEvent_0qomvov", "IntermediateThrowEvent_0xjpikb", "IntermediateThrowEvent_0neineb", "Task_002ndsu", "Task_1ne4gpy", "EndEvent_1vkzo14" }
  @@ "TravelAgency_" :> { "BoundaryEvent_19y0yk9", "EndEvent_17rlcaz", "EndEvent_10gqkzy", "SubProcess_1agd6n3", "Activity_0re3cuj", "StartEvent_1f3jj6d", "BoundaryEvent_0j1yvnw", "IntermediateThrowEvent_0b4rm53" }

Node == { "Customer_", "TravelAgency_", "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "EndEvent_0u6deep", "IntermediateThrowEvent_12d113r", "Task_1q91vog", "BoundaryEvent_0qlhw6m", "EndEvent_0syu44v", "IntermediateThrowEvent_02q48nh", "BoundaryEvent_19y0yk9", "EndEvent_17rlcaz", "EndEvent_10gqkzy", "SubProcess_1agd6n3", "Activity_0re3cuj", "StartEvent_1f3jj6d", "BoundaryEvent_0j1yvnw", "IntermediateThrowEvent_0b4rm53", "StartEvent_0qomvov", "IntermediateThrowEvent_0xjpikb", "IntermediateThrowEvent_0neineb", "Task_002ndsu", "Task_1ne4gpy", "EndEvent_1vkzo14", "Event_0e98cce", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q" }

Edge == { "MessageFlow_0knd10s", "MessageFlow_1yfhhru", "MessageFlow_1m551dh", "MessageFlow_1goz1mt", "MessageFlow_04an7oz", "MessageFlow_18qwt5e", "Flow_03c8rm0", "SequenceFlow_1uwq0b6", "SequenceFlow_0b6ku63", "SequenceFlow_0sfyd5z", "SequenceFlow_016h32p", "SequenceFlow_1rma3l8", "SequenceFlow_1dptcxp", "SequenceFlow_1h5h7h5", "SequenceFlow_0ljbxox", "SequenceFlow_1qku5do", "SequenceFlow_1pk6qce", "SequenceFlow_0ybs6n8", "SequenceFlow_1yvkisw", "SequenceFlow_1oyuvjd", "Flow_136sol6", "Flow_0y4msh1", "Flow_1n9oaui", "SequenceFlow_17r8ru7", "SequenceFlow_1j6r6o5", "SequenceFlow_0bejayl", "SequenceFlow_0ot5p93", "SequenceFlow_023db5j", "Flow_0ugr6x2", "Flow_11b0t0o", "Flow_14ugxng" }

Message == { "Offer", "Travel", "Confirmation", "Payment", "Ticket", "Abort", "NoMore" }

msgtype ==
   "MessageFlow_0knd10s" :> "Offer"
@@ "MessageFlow_1yfhhru" :> "Travel"
@@ "MessageFlow_1m551dh" :> "Confirmation"
@@ "MessageFlow_1goz1mt" :> "Payment"
@@ "MessageFlow_04an7oz" :> "Ticket"
@@ "MessageFlow_18qwt5e" :> "Abort"
@@ "Flow_03c8rm0" :> "NoMore"


source ==
   "MessageFlow_0knd10s" :> "Task_1bn6n5q"
@@ "MessageFlow_1yfhhru" :> "Task_1v9s881"
@@ "MessageFlow_1m551dh" :> "Task_002ndsu"
@@ "MessageFlow_1goz1mt" :> "Task_1q91vog"
@@ "MessageFlow_04an7oz" :> "Task_1ne4gpy"
@@ "MessageFlow_18qwt5e" :> "IntermediateThrowEvent_02q48nh"
@@ "Flow_03c8rm0" :> "IntermediateThrowEvent_0b4rm53"
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
@@ "SequenceFlow_1yvkisw" :> "SubProcess_1agd6n3"
@@ "SequenceFlow_1oyuvjd" :> "BoundaryEvent_19y0yk9"
@@ "Flow_136sol6" :> "StartEvent_1f3jj6d"
@@ "Flow_0y4msh1" :> "BoundaryEvent_0j1yvnw"
@@ "Flow_1n9oaui" :> "IntermediateThrowEvent_0b4rm53"
@@ "SequenceFlow_17r8ru7" :> "StartEvent_0qomvov"
@@ "SequenceFlow_1j6r6o5" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_0bejayl" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_0ot5p93" :> "Task_002ndsu"
@@ "SequenceFlow_023db5j" :> "Task_1ne4gpy"
@@ "Flow_0ugr6x2" :> "Event_0e98cce"
@@ "Flow_11b0t0o" :> "ExclusiveGateway_1dc5v3z"
@@ "Flow_14ugxng" :> "Task_1bn6n5q"

target ==
   "MessageFlow_0knd10s" :> "Task_07u875a"
@@ "MessageFlow_1yfhhru" :> "IntermediateThrowEvent_0xjpikb"
@@ "MessageFlow_1m551dh" :> "EndEvent_0u6deep"
@@ "MessageFlow_1goz1mt" :> "IntermediateThrowEvent_0neineb"
@@ "MessageFlow_04an7oz" :> "IntermediateThrowEvent_12d113r"
@@ "MessageFlow_18qwt5e" :> "BoundaryEvent_19y0yk9"
@@ "Flow_03c8rm0" :> "BoundaryEvent_0qlhw6m"
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
@@ "SequenceFlow_1yvkisw" :> "EndEvent_10gqkzy"
@@ "SequenceFlow_1oyuvjd" :> "EndEvent_17rlcaz"
@@ "Flow_136sol6" :> "Activity_0re3cuj"
@@ "Flow_0y4msh1" :> "IntermediateThrowEvent_0b4rm53"
@@ "Flow_1n9oaui" :> "SubProcess_1agd6n3"
@@ "SequenceFlow_17r8ru7" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_1j6r6o5" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_0bejayl" :> "Task_002ndsu"
@@ "SequenceFlow_0ot5p93" :> "Task_1ne4gpy"
@@ "SequenceFlow_023db5j" :> "EndEvent_1vkzo14"
@@ "Flow_0ugr6x2" :> "ExclusiveGateway_1dc5v3z"
@@ "Flow_11b0t0o" :> "Task_1bn6n5q"
@@ "Flow_14ugxng" :> "ExclusiveGateway_1dc5v3z"

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
@@ "BoundaryEvent_19y0yk9" :> MessageBoundaryEvent
@@ "EndEvent_17rlcaz" :> NoneEndEvent
@@ "EndEvent_10gqkzy" :> NoneEndEvent
@@ "SubProcess_1agd6n3" :> SubProcess
@@ "Activity_0re3cuj" :> SubProcess
@@ "StartEvent_1f3jj6d" :> NoneStartEvent
@@ "BoundaryEvent_0j1yvnw" :> TimerBoundaryEvent
@@ "IntermediateThrowEvent_0b4rm53" :> ThrowMessageIntermediateEvent
@@ "StartEvent_0qomvov" :> NoneStartEvent
@@ "IntermediateThrowEvent_0xjpikb" :> CatchMessageIntermediateEvent
@@ "IntermediateThrowEvent_0neineb" :> CatchMessageIntermediateEvent
@@ "Task_002ndsu" :> SendTask
@@ "Task_1ne4gpy" :> SendTask
@@ "EndEvent_1vkzo14" :> NoneEndEvent
@@ "Event_0e98cce" :> NoneStartEvent
@@ "ExclusiveGateway_1dc5v3z" :> ExclusiveOr
@@ "Task_1bn6n5q" :> SendTask

CatE ==
   "MessageFlow_0knd10s" :> MessageFlow
@@ "MessageFlow_1yfhhru" :> MessageFlow
@@ "MessageFlow_1m551dh" :> MessageFlow
@@ "MessageFlow_1goz1mt" :> MessageFlow
@@ "MessageFlow_04an7oz" :> MessageFlow
@@ "MessageFlow_18qwt5e" :> MessageFlow
@@ "Flow_03c8rm0" :> MessageFlow
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
@@ "SequenceFlow_1yvkisw" :> NormalSeqFlow
@@ "SequenceFlow_1oyuvjd" :> NormalSeqFlow
@@ "Flow_136sol6" :> NormalSeqFlow
@@ "Flow_0y4msh1" :> NormalSeqFlow
@@ "Flow_1n9oaui" :> NormalSeqFlow
@@ "SequenceFlow_17r8ru7" :> NormalSeqFlow
@@ "SequenceFlow_1j6r6o5" :> NormalSeqFlow
@@ "SequenceFlow_0bejayl" :> NormalSeqFlow
@@ "SequenceFlow_0ot5p93" :> NormalSeqFlow
@@ "SequenceFlow_023db5j" :> NormalSeqFlow
@@ "Flow_0ugr6x2" :> NormalSeqFlow
@@ "Flow_11b0t0o" :> NormalSeqFlow
@@ "Flow_14ugxng" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_0qlhw6m" :> [ attachedTo |-> "Task_07u875a", cancelActivity |-> TRUE ]
@@ "BoundaryEvent_19y0yk9" :> [ attachedTo |-> "SubProcess_1agd6n3", cancelActivity |-> TRUE ]
@@ "BoundaryEvent_0j1yvnw" :> [ attachedTo |-> "Activity_0re3cuj", cancelActivity |-> TRUE ]

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

