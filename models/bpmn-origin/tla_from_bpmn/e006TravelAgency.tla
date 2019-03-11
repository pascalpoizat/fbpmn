---------------- MODULE e006TravelAgency ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_1" :> { "Task_1v9s881", "ExclusiveGateway_192ovii", "ExclusiveGateway_0wgdt1i", "StartEvent_1", "Task_07u875a", "EndEvent_055yt9k", "EndEvent_0u6deep", "Task_1q91vog", "IntermediateThrowEvent_12d113r" }
  @@ "Process_14x2mcf" :> { "StartEvent_1f3jj6d", "ExclusiveGateway_1dc5v3z", "Task_1bn6n5q", "ExclusiveGateway_0i09ijx", "IntermediateThrowEvent_0xjpikb", "EndEvent_10gqkzy", "Task_1ne4gpy", "Task_002ndsu", "IntermediateThrowEvent_0neineb" }

Node == {
  "Process_1","Process_14x2mcf","Task_1v9s881","ExclusiveGateway_192ovii","ExclusiveGateway_0wgdt1i","StartEvent_1","Task_07u875a","EndEvent_055yt9k","EndEvent_0u6deep","Task_1q91vog","IntermediateThrowEvent_12d113r","StartEvent_1f3jj6d","ExclusiveGateway_1dc5v3z","Task_1bn6n5q","ExclusiveGateway_0i09ijx","IntermediateThrowEvent_0xjpikb","EndEvent_10gqkzy","Task_1ne4gpy","Task_002ndsu","IntermediateThrowEvent_0neineb"
}

Edge == {
  "MessageFlow_0knd10s","MessageFlow_1yfhhru","MessageFlow_1m551dh","MessageFlow_1goz1mt","MessageFlow_04an7oz","SequenceFlow_1uwq0b6","SequenceFlow_0b6ku63","SequenceFlow_0sfyd5z","SequenceFlow_016h32p","SequenceFlow_1rma3l8","SequenceFlow_1dptcxp","SequenceFlow_1h5h7h5","SequenceFlow_0ljbxox","SequenceFlow_1qku5do","SequenceFlow_1fn4lqy","SequenceFlow_0b34324","SequenceFlow_0mdvaai","SequenceFlow_13z4ilm","SequenceFlow_0rfye55","SequenceFlow_1rlj8av","SequenceFlow_0n80biv","SequenceFlow_00s838q","SequenceFlow_11rxzkm"
}

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
@@ "SequenceFlow_1uwq0b6" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_0sfyd5z" :> "Task_07u875a"
@@ "SequenceFlow_016h32p" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1rma3l8" :> "StartEvent_1"
@@ "SequenceFlow_1dptcxp" :> "Task_1v9s881"
@@ "SequenceFlow_1h5h7h5" :> "Task_1q91vog"
@@ "SequenceFlow_0ljbxox" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_1qku5do" :> "EndEvent_0u6deep"
@@ "SequenceFlow_1fn4lqy" :> "StartEvent_1f3jj6d"
@@ "SequenceFlow_0b34324" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0mdvaai" :> "Task_1bn6n5q"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_0rfye55" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_1rlj8av" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_0n80biv" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_00s838q" :> "Task_002ndsu"
@@ "SequenceFlow_11rxzkm" :> "Task_1ne4gpy"

target ==
   "MessageFlow_0knd10s" :> "Task_07u875a"
@@ "MessageFlow_1yfhhru" :> "IntermediateThrowEvent_0xjpikb"
@@ "MessageFlow_1m551dh" :> "EndEvent_0u6deep"
@@ "MessageFlow_1goz1mt" :> "IntermediateThrowEvent_0neineb"
@@ "MessageFlow_04an7oz" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_1uwq0b6" :> "Task_1v9s881"
@@ "SequenceFlow_0b6ku63" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_0sfyd5z" :> "ExclusiveGateway_192ovii"
@@ "SequenceFlow_016h32p" :> "Task_07u875a"
@@ "SequenceFlow_1rma3l8" :> "ExclusiveGateway_0wgdt1i"
@@ "SequenceFlow_1dptcxp" :> "Task_1q91vog"
@@ "SequenceFlow_1h5h7h5" :> "IntermediateThrowEvent_12d113r"
@@ "SequenceFlow_0ljbxox" :> "EndEvent_0u6deep"
@@ "SequenceFlow_1qku5do" :> "EndEvent_055yt9k"
@@ "SequenceFlow_1fn4lqy" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0b34324" :> "Task_1bn6n5q"
@@ "SequenceFlow_0mdvaai" :> "ExclusiveGateway_0i09ijx"
@@ "SequenceFlow_13z4ilm" :> "ExclusiveGateway_1dc5v3z"
@@ "SequenceFlow_0rfye55" :> "IntermediateThrowEvent_0xjpikb"
@@ "SequenceFlow_1rlj8av" :> "IntermediateThrowEvent_0neineb"
@@ "SequenceFlow_0n80biv" :> "Task_002ndsu"
@@ "SequenceFlow_00s838q" :> "Task_1ne4gpy"
@@ "SequenceFlow_11rxzkm" :> "EndEvent_10gqkzy"

CatN ==
   "Process_1" :> Process
@@ "Process_14x2mcf" :> Process
@@ "Task_1v9s881" :> SendTask
@@ "ExclusiveGateway_192ovii" :> ExclusiveOr
@@ "ExclusiveGateway_0wgdt1i" :> ExclusiveOr
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_07u875a" :> ReceiveTask
@@ "EndEvent_055yt9k" :> NoneEndEvent
@@ "EndEvent_0u6deep" :> CatchMessageIntermediateEvent
@@ "Task_1q91vog" :> SendTask
@@ "IntermediateThrowEvent_12d113r" :> CatchMessageIntermediateEvent
@@ "StartEvent_1f3jj6d" :> NoneStartEvent
@@ "ExclusiveGateway_1dc5v3z" :> ExclusiveOr
@@ "Task_1bn6n5q" :> SendTask
@@ "ExclusiveGateway_0i09ijx" :> Parallel
@@ "IntermediateThrowEvent_0xjpikb" :> CatchMessageIntermediateEvent
@@ "EndEvent_10gqkzy" :> NoneEndEvent
@@ "Task_1ne4gpy" :> SendTask
@@ "Task_002ndsu" :> SendTask
@@ "IntermediateThrowEvent_0neineb" :> CatchMessageIntermediateEvent

CatE ==
   "MessageFlow_0knd10s" :> MsgFlow
@@ "MessageFlow_1yfhhru" :> MsgFlow
@@ "MessageFlow_1m551dh" :> MsgFlow
@@ "MessageFlow_1goz1mt" :> MsgFlow
@@ "MessageFlow_04an7oz" :> MsgFlow
@@ "SequenceFlow_1uwq0b6" :> ConditionalSeqFlow
@@ "SequenceFlow_0b6ku63" :> ConditionalSeqFlow
@@ "SequenceFlow_0sfyd5z" :> NormalSeqFlow
@@ "SequenceFlow_016h32p" :> NormalSeqFlow
@@ "SequenceFlow_1rma3l8" :> NormalSeqFlow
@@ "SequenceFlow_1dptcxp" :> NormalSeqFlow
@@ "SequenceFlow_1h5h7h5" :> NormalSeqFlow
@@ "SequenceFlow_0ljbxox" :> NormalSeqFlow
@@ "SequenceFlow_1qku5do" :> NormalSeqFlow
@@ "SequenceFlow_1fn4lqy" :> NormalSeqFlow
@@ "SequenceFlow_0b34324" :> NormalSeqFlow
@@ "SequenceFlow_0mdvaai" :> NormalSeqFlow
@@ "SequenceFlow_13z4ilm" :> NormalSeqFlow
@@ "SequenceFlow_0rfye55" :> NormalSeqFlow
@@ "SequenceFlow_1rlj8av" :> NormalSeqFlow
@@ "SequenceFlow_0n80biv" :> NormalSeqFlow
@@ "SequenceFlow_00s838q" :> NormalSeqFlow
@@ "SequenceFlow_11rxzkm" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

