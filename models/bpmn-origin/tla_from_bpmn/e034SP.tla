---------------- MODULE e034SP ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> {  }

ContainRel ==
  "P_" :> { "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28" }
  @@ "SubProcess_1glz8ii" :> { "StartEvent_09ojxru", "StartEvent_0p1e2cq", "Task_1x5zvyz", "EndEvent_0atuxkh", "ExclusiveGateway_0vdfgj4" }

Node == { "P_", "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28", "StartEvent_09ojxru", "StartEvent_0p1e2cq", "Task_1x5zvyz", "EndEvent_0atuxkh", "ExclusiveGateway_0vdfgj4" }

Edge == { "SequenceFlow_12utbfs", "SequenceFlow_00j4ong", "SequenceFlow_19k9u87", "SequenceFlow_1t5jo8c", "SequenceFlow_04a621f", "SequenceFlow_1uo79pd" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_12utbfs" :> "StartEvent_1"
@@ "SequenceFlow_00j4ong" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_19k9u87" :> "StartEvent_09ojxru"
@@ "SequenceFlow_1t5jo8c" :> "StartEvent_0p1e2cq"
@@ "SequenceFlow_04a621f" :> "ExclusiveGateway_0vdfgj4"
@@ "SequenceFlow_1uo79pd" :> "Task_1x5zvyz"

target ==
   "SequenceFlow_12utbfs" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_00j4ong" :> "EndEvent_0a59w28"
@@ "SequenceFlow_19k9u87" :> "ExclusiveGateway_0vdfgj4"
@@ "SequenceFlow_1t5jo8c" :> "ExclusiveGateway_0vdfgj4"
@@ "SequenceFlow_04a621f" :> "Task_1x5zvyz"
@@ "SequenceFlow_1uo79pd" :> "EndEvent_0atuxkh"

CatN ==
   "P_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "SubProcess_1glz8ii" :> SubProcess
@@ "EndEvent_0a59w28" :> NoneEndEvent
@@ "StartEvent_09ojxru" :> NoneStartEvent
@@ "StartEvent_0p1e2cq" :> NoneStartEvent
@@ "Task_1x5zvyz" :> AbstractTask
@@ "EndEvent_0atuxkh" :> NoneEndEvent
@@ "ExclusiveGateway_0vdfgj4" :> ExclusiveOr

CatE ==
   "SequenceFlow_12utbfs" :> NormalSeqFlow
@@ "SequenceFlow_00j4ong" :> NormalSeqFlow
@@ "SequenceFlow_19k9u87" :> NormalSeqFlow
@@ "SequenceFlow_1t5jo8c" :> NormalSeqFlow
@@ "SequenceFlow_04a621f" :> NormalSeqFlow
@@ "SequenceFlow_1uo79pd" :> NormalSeqFlow

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

