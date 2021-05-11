---------------- MODULE e051TBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_1" :> {  }

ContainRel ==
  "Process_1" :> { "StartEvent_1", "Task_1s6tj7r", "BoundaryEvent_0r0bcez", "EndEvent_08uegvd", "EndEvent_14srvev" }

Node == { "Process_1", "StartEvent_1", "Task_1s6tj7r", "BoundaryEvent_0r0bcez", "EndEvent_08uegvd", "EndEvent_14srvev" }

Edge == { "SequenceFlow_0yeopwj", "SequenceFlow_1131nmm", "SequenceFlow_1co9zfu" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_0yeopwj" :> "StartEvent_1"
@@ "SequenceFlow_1131nmm" :> "Task_1s6tj7r"
@@ "SequenceFlow_1co9zfu" :> "BoundaryEvent_0r0bcez"

target ==
   "SequenceFlow_0yeopwj" :> "Task_1s6tj7r"
@@ "SequenceFlow_1131nmm" :> "EndEvent_14srvev"
@@ "SequenceFlow_1co9zfu" :> "EndEvent_08uegvd"

CatN ==
   "Process_1" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_1s6tj7r" :> AbstractTask
@@ "BoundaryEvent_0r0bcez" :> TimerBoundaryEvent
@@ "EndEvent_08uegvd" :> NoneEndEvent
@@ "EndEvent_14srvev" :> TerminateEndEvent

CatE ==
   "SequenceFlow_0yeopwj" :> NormalSeqFlow
@@ "SequenceFlow_1131nmm" :> NormalSeqFlow
@@ "SequenceFlow_1co9zfu" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_0r0bcez" :> [ attachedTo |-> "Task_1s6tj7r", cancelActivity |-> TRUE ]

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

