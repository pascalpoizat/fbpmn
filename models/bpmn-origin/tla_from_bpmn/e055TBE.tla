---------------- MODULE e055TBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_1" :> {  }

ContainRel ==
  "Process_1" :> { "SubProcess_0h2vtyo", "BoundaryEvent_02b1vw4", "StartEvent_1", "EndEvent_111i3i3" }
  @@ "SubProcess_0h2vtyo" :> { "StartEvent_0hi510e", "Task_0mfb6xu", "Task_0m7n5xk" }

Node == { "Process_1", "SubProcess_0h2vtyo", "BoundaryEvent_02b1vw4", "StartEvent_1", "EndEvent_111i3i3", "StartEvent_0hi510e", "Task_0mfb6xu", "Task_0m7n5xk" }

Edge == { "SequenceFlow_1tuej2e", "SequenceFlow_05shv4u", "SequenceFlow_1y9pakp", "SequenceFlow_19ibfph", "SequenceFlow_038z5pz" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_1tuej2e" :> "BoundaryEvent_02b1vw4"
@@ "SequenceFlow_05shv4u" :> "StartEvent_1"
@@ "SequenceFlow_1y9pakp" :> "StartEvent_0hi510e"
@@ "SequenceFlow_19ibfph" :> "Task_0mfb6xu"
@@ "SequenceFlow_038z5pz" :> "Task_0m7n5xk"

target ==
   "SequenceFlow_1tuej2e" :> "EndEvent_111i3i3"
@@ "SequenceFlow_05shv4u" :> "SubProcess_0h2vtyo"
@@ "SequenceFlow_1y9pakp" :> "Task_0mfb6xu"
@@ "SequenceFlow_19ibfph" :> "Task_0m7n5xk"
@@ "SequenceFlow_038z5pz" :> "Task_0mfb6xu"

CatN ==
   "Process_1" :> Process
@@ "SubProcess_0h2vtyo" :> SubProcess
@@ "BoundaryEvent_02b1vw4" :> TimerBoundaryEvent
@@ "StartEvent_1" :> NoneStartEvent
@@ "EndEvent_111i3i3" :> NoneEndEvent
@@ "StartEvent_0hi510e" :> NoneStartEvent
@@ "Task_0mfb6xu" :> AbstractTask
@@ "Task_0m7n5xk" :> AbstractTask

CatE ==
   "SequenceFlow_1tuej2e" :> NormalSeqFlow
@@ "SequenceFlow_05shv4u" :> NormalSeqFlow
@@ "SequenceFlow_1y9pakp" :> NormalSeqFlow
@@ "SequenceFlow_19ibfph" :> NormalSeqFlow
@@ "SequenceFlow_038z5pz" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_02b1vw4" :> [ attachedTo |-> "SubProcess_0h2vtyo", cancelActivity |-> TRUE ]

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

