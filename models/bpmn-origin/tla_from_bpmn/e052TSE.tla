---------------- MODULE e052TSE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_1" :> {  }

ContainRel ==
  "Process_1" :> { "EndEvent_14srvev", "Task_0r3p2er", "StartEvent_1" }

Node == { "Process_1", "EndEvent_14srvev", "Task_0r3p2er", "StartEvent_1" }

Edge == { "SequenceFlow_0yeopwj", "SequenceFlow_1tn9sj7" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_0yeopwj" :> "StartEvent_1"
@@ "SequenceFlow_1tn9sj7" :> "Task_0r3p2er"

target ==
   "SequenceFlow_0yeopwj" :> "Task_0r3p2er"
@@ "SequenceFlow_1tn9sj7" :> "EndEvent_14srvev"

CatN ==
   "Process_1" :> Process
@@ "EndEvent_14srvev" :> NoneEndEvent
@@ "Task_0r3p2er" :> AbstractTask
@@ "StartEvent_1" :> TimerStartEvent

CatE ==
   "SequenceFlow_0yeopwj" :> NormalSeqFlow
@@ "SequenceFlow_1tn9sj7" :> NormalSeqFlow

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

