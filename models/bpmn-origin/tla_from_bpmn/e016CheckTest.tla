---------------- MODULE e016CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Receiver_" :> { "m1", "m2" }
  @@ "Sender_" :> {  }

ContainRel ==
  "Receiver_" :> { "StartEvent_0x0o2ml", "EndEvent_1d6yy2u", "EndEvent_19gcpb9", "Task_1d78ih0", "Task_19wi6kk", "ExclusiveGateway_1aidani" }
  @@ "Sender_" :> { "StartEvent_1", "ExclusiveGateway_1gus05a", "EndEvent_198u4gq", "EndEvent_1e5c16l", "Task_1c559zv", "Task_1cbrss1" }

Node == { "Sender_", "Receiver_", "StartEvent_1", "ExclusiveGateway_1gus05a", "EndEvent_198u4gq", "EndEvent_1e5c16l", "Task_1c559zv", "Task_1cbrss1", "StartEvent_0x0o2ml", "EndEvent_1d6yy2u", "EndEvent_19gcpb9", "Task_1d78ih0", "Task_19wi6kk", "ExclusiveGateway_1aidani" }

Edge == { "MessageFlow_095vt4e", "MessageFlow_1n4m463", "SequenceFlow_1bot7ik", "SequenceFlow_1t3w3h5", "SequenceFlow_13vrdzd", "SequenceFlow_08o2r31", "SequenceFlow_0cvzouu", "SequenceFlow_0fxw5l8", "SequenceFlow_01czfja", "SequenceFlow_0qoid9s", "SequenceFlow_0ob8kjq", "SequenceFlow_0tmjk0x" }

Message == { "m1", "m2" }

msgtype ==
   "MessageFlow_095vt4e" :> "m1"
@@ "MessageFlow_1n4m463" :> "m2"


source ==
   "MessageFlow_095vt4e" :> "Task_1c559zv"
@@ "MessageFlow_1n4m463" :> "Task_1cbrss1"
@@ "SequenceFlow_1bot7ik" :> "StartEvent_1"
@@ "SequenceFlow_1t3w3h5" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_13vrdzd" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_08o2r31" :> "Task_1cbrss1"
@@ "SequenceFlow_0cvzouu" :> "Task_1c559zv"
@@ "SequenceFlow_0fxw5l8" :> "StartEvent_0x0o2ml"
@@ "SequenceFlow_01czfja" :> "ExclusiveGateway_1aidani"
@@ "SequenceFlow_0qoid9s" :> "ExclusiveGateway_1aidani"
@@ "SequenceFlow_0ob8kjq" :> "Task_1d78ih0"
@@ "SequenceFlow_0tmjk0x" :> "Task_19wi6kk"

target ==
   "MessageFlow_095vt4e" :> "Task_1d78ih0"
@@ "MessageFlow_1n4m463" :> "Task_19wi6kk"
@@ "SequenceFlow_1bot7ik" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_1t3w3h5" :> "Task_1c559zv"
@@ "SequenceFlow_13vrdzd" :> "Task_1cbrss1"
@@ "SequenceFlow_08o2r31" :> "EndEvent_198u4gq"
@@ "SequenceFlow_0cvzouu" :> "EndEvent_1e5c16l"
@@ "SequenceFlow_0fxw5l8" :> "ExclusiveGateway_1aidani"
@@ "SequenceFlow_01czfja" :> "Task_1d78ih0"
@@ "SequenceFlow_0qoid9s" :> "Task_19wi6kk"
@@ "SequenceFlow_0ob8kjq" :> "EndEvent_1d6yy2u"
@@ "SequenceFlow_0tmjk0x" :> "EndEvent_19gcpb9"

CatN ==
   "Sender_" :> Process
@@ "Receiver_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_1gus05a" :> ExclusiveOr
@@ "EndEvent_198u4gq" :> NoneEndEvent
@@ "EndEvent_1e5c16l" :> NoneEndEvent
@@ "Task_1c559zv" :> SendTask
@@ "Task_1cbrss1" :> SendTask
@@ "StartEvent_0x0o2ml" :> NoneStartEvent
@@ "EndEvent_1d6yy2u" :> NoneEndEvent
@@ "EndEvent_19gcpb9" :> NoneEndEvent
@@ "Task_1d78ih0" :> ReceiveTask
@@ "Task_19wi6kk" :> ReceiveTask
@@ "ExclusiveGateway_1aidani" :> EventBased

CatE ==
   "MessageFlow_095vt4e" :> MessageFlow
@@ "MessageFlow_1n4m463" :> MessageFlow
@@ "SequenceFlow_1bot7ik" :> NormalSeqFlow
@@ "SequenceFlow_1t3w3h5" :> ConditionalSeqFlow
@@ "SequenceFlow_13vrdzd" :> DefaultSeqFlow
@@ "SequenceFlow_08o2r31" :> NormalSeqFlow
@@ "SequenceFlow_0cvzouu" :> NormalSeqFlow
@@ "SequenceFlow_0fxw5l8" :> NormalSeqFlow
@@ "SequenceFlow_01czfja" :> NormalSeqFlow
@@ "SequenceFlow_0qoid9s" :> NormalSeqFlow
@@ "SequenceFlow_0ob8kjq" :> NormalSeqFlow
@@ "SequenceFlow_0tmjk0x" :> NormalSeqFlow

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

