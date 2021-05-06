---------------- MODULE e014CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_" :> {  }

ContainRel ==
  "Process_" :> { "StartEvent_1", "ExclusiveGateway_1gus05a", "Task_1c559zv", "Task_1cbrss1", "EndEvent_198u4gq", "EndEvent_1e5c16l" }

Node == { "Process_", "StartEvent_1", "ExclusiveGateway_1gus05a", "Task_1c559zv", "Task_1cbrss1", "EndEvent_198u4gq", "EndEvent_1e5c16l" }

Edge == { "SequenceFlow_1bot7ik", "SequenceFlow_1t3w3h5", "SequenceFlow_13vrdzd", "SequenceFlow_08o2r31", "SequenceFlow_0cvzouu" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_1bot7ik" :> "StartEvent_1"
@@ "SequenceFlow_1t3w3h5" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_13vrdzd" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_08o2r31" :> "Task_1cbrss1"
@@ "SequenceFlow_0cvzouu" :> "Task_1c559zv"

target ==
   "SequenceFlow_1bot7ik" :> "ExclusiveGateway_1gus05a"
@@ "SequenceFlow_1t3w3h5" :> "Task_1c559zv"
@@ "SequenceFlow_13vrdzd" :> "Task_1cbrss1"
@@ "SequenceFlow_08o2r31" :> "EndEvent_198u4gq"
@@ "SequenceFlow_0cvzouu" :> "EndEvent_1e5c16l"

CatN ==
   "Process_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_1gus05a" :> ExclusiveOr
@@ "Task_1c559zv" :> AbstractTask
@@ "Task_1cbrss1" :> AbstractTask
@@ "EndEvent_198u4gq" :> NoneEndEvent
@@ "EndEvent_1e5c16l" :> NoneEndEvent

CatE ==
   "SequenceFlow_1bot7ik" :> NormalSeqFlow
@@ "SequenceFlow_1t3w3h5" :> ConditionalSeqFlow
@@ "SequenceFlow_13vrdzd" :> DefaultSeqFlow
@@ "SequenceFlow_08o2r31" :> NormalSeqFlow
@@ "SequenceFlow_0cvzouu" :> NormalSeqFlow

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

