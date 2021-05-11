---------------- MODULE e050TIE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_1" :> {  }

ContainRel ==
  "Process_1" :> { "EndEvent_14srvev", "StartEvent_1", "IntermediateThrowEvent_1l1btga" }

Node == { "Process_1", "EndEvent_14srvev", "StartEvent_1", "IntermediateThrowEvent_1l1btga" }

Edge == { "SequenceFlow_0yeopwj", "SequenceFlow_04ghp5z" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_0yeopwj" :> "StartEvent_1"
@@ "SequenceFlow_04ghp5z" :> "IntermediateThrowEvent_1l1btga"

target ==
   "SequenceFlow_0yeopwj" :> "IntermediateThrowEvent_1l1btga"
@@ "SequenceFlow_04ghp5z" :> "EndEvent_14srvev"

CatN ==
   "Process_1" :> Process
@@ "EndEvent_14srvev" :> NoneEndEvent
@@ "StartEvent_1" :> NoneStartEvent
@@ "IntermediateThrowEvent_1l1btga" :> TimerIntermediateEvent

CatE ==
   "SequenceFlow_0yeopwj" :> NormalSeqFlow
@@ "SequenceFlow_04ghp5z" :> NormalSeqFlow

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

