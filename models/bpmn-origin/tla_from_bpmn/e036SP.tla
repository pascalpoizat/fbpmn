---------------- MODULE e036SP ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> {  }

ContainRel ==
  "P_" :> { "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28" }
  @@ "SubProcess_1glz8ii" :> { "StartEvent_09ojxru", "EndEvent_0atuxkh", "EndEvent_1bu7x75", "ExclusiveGateway_1449jmr" }

Node == { "P_", "StartEvent_1", "SubProcess_1glz8ii", "EndEvent_0a59w28", "StartEvent_09ojxru", "EndEvent_0atuxkh", "EndEvent_1bu7x75", "ExclusiveGateway_1449jmr" }

Edge == { "SequenceFlow_12utbfs", "SequenceFlow_00j4ong", "SequenceFlow_1yn4txk", "SequenceFlow_0xc489r", "SequenceFlow_1ue74ws" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_12utbfs" :> "StartEvent_1"
@@ "SequenceFlow_00j4ong" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_1yn4txk" :> "StartEvent_09ojxru"
@@ "SequenceFlow_0xc489r" :> "ExclusiveGateway_1449jmr"
@@ "SequenceFlow_1ue74ws" :> "ExclusiveGateway_1449jmr"

target ==
   "SequenceFlow_12utbfs" :> "SubProcess_1glz8ii"
@@ "SequenceFlow_00j4ong" :> "EndEvent_0a59w28"
@@ "SequenceFlow_1yn4txk" :> "ExclusiveGateway_1449jmr"
@@ "SequenceFlow_0xc489r" :> "EndEvent_0atuxkh"
@@ "SequenceFlow_1ue74ws" :> "EndEvent_1bu7x75"

CatN ==
   "P_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "SubProcess_1glz8ii" :> SubProcess
@@ "EndEvent_0a59w28" :> NoneEndEvent
@@ "StartEvent_09ojxru" :> NoneStartEvent
@@ "EndEvent_0atuxkh" :> NoneEndEvent
@@ "EndEvent_1bu7x75" :> NoneEndEvent
@@ "ExclusiveGateway_1449jmr" :> Parallel

CatE ==
   "SequenceFlow_12utbfs" :> NormalSeqFlow
@@ "SequenceFlow_00j4ong" :> NormalSeqFlow
@@ "SequenceFlow_1yn4txk" :> NormalSeqFlow
@@ "SequenceFlow_0xc489r" :> NormalSeqFlow
@@ "SequenceFlow_1ue74ws" :> NormalSeqFlow

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

