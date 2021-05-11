---------------- MODULE e035SP ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> { "m1" }
  @@ "Q_" :> {  }

ContainRel ==
  "P_" :> { "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28" }
  @@ "Q_" :> { "StartEvent_0943q6x", "EndEvent_1jzyo34", "Task_0mft1gb" }
  @@ "SubProcess_1glz8ii" :> { "Task_1x5zvyz", "EndEvent_0atuxkh", "StartEvent_09ojxru" }

Node == { "P_", "Q_", "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28", "Task_1x5zvyz", "EndEvent_0atuxkh", "StartEvent_09ojxru", "StartEvent_0943q6x", "EndEvent_1jzyo34", "Task_0mft1gb" }

Edge == { "MessageFlow_183e2wp", "SequenceFlow_12utbfs", "SequenceFlow_00j4ong", "SequenceFlow_1uo79pd", "SequenceFlow_0yhgli1", "SequenceFlow_11rsxtg", "SequenceFlow_0pgod6g" }

Message == { "m1" }

msgtype ==
   "MessageFlow_183e2wp" :> "m1"


source ==
   "MessageFlow_183e2wp" :> "Task_0mft1gb"
@@ "SequenceFlow_12utbfs" :> "StartEvent_1"
@@ "SequenceFlow_00j4ong" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_1uo79pd" :> "Task_1x5zvyz"
@@ "SequenceFlow_0yhgli1" :> "StartEvent_09ojxru"
@@ "SequenceFlow_11rsxtg" :> "StartEvent_0943q6x"
@@ "SequenceFlow_0pgod6g" :> "Task_0mft1gb"

target ==
   "MessageFlow_183e2wp" :> "StartEvent_09ojxru"
@@ "SequenceFlow_12utbfs" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_00j4ong" :> "EndEvent_0a59w28"
@@ "SequenceFlow_1uo79pd" :> "EndEvent_0atuxkh"
@@ "SequenceFlow_0yhgli1" :> "Task_1x5zvyz"
@@ "SequenceFlow_11rsxtg" :> "Task_0mft1gb"
@@ "SequenceFlow_0pgod6g" :> "EndEvent_1jzyo34"

CatN ==
   "P_" :> Process
@@ "Q_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "SubProcess_1glz8ii" :> SubProcess
@@ "EndEvent_0a59w28" :> NoneEndEvent
@@ "Task_1x5zvyz" :> AbstractTask
@@ "EndEvent_0atuxkh" :> NoneEndEvent
@@ "StartEvent_09ojxru" :> MessageStartEvent
@@ "StartEvent_0943q6x" :> NoneStartEvent
@@ "EndEvent_1jzyo34" :> NoneEndEvent
@@ "Task_0mft1gb" :> SendTask

CatE ==
   "MessageFlow_183e2wp" :> MessageFlow
@@ "SequenceFlow_12utbfs" :> NormalSeqFlow
@@ "SequenceFlow_00j4ong" :> NormalSeqFlow
@@ "SequenceFlow_1uo79pd" :> NormalSeqFlow
@@ "SequenceFlow_0yhgli1" :> NormalSeqFlow
@@ "SequenceFlow_11rsxtg" :> NormalSeqFlow
@@ "SequenceFlow_0pgod6g" :> NormalSeqFlow

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

