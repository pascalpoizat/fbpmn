---------------- MODULE e009CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "A_" :> {  }
  @@ "B_" :> { "m1" }

ContainRel ==
  "A_" :> { "Task_097548f", "Task_1eirt50", "ExclusiveGateway_0079typ", "EndEvent_0v9lt5i", "ExclusiveGateway_1j1chqb", "StartEvent_1", "Task_1rt44mz" }
  @@ "B_" :> { "StartEvent_1wwcoxd", "EndEvent_1wbcvef", "Task_18t09mk" }

Node == { "A_", "B_", "Task_097548f", "Task_1eirt50", "ExclusiveGateway_0079typ", "EndEvent_0v9lt5i", "ExclusiveGateway_1j1chqb", "StartEvent_1", "Task_1rt44mz", "StartEvent_1wwcoxd", "EndEvent_1wbcvef", "Task_18t09mk" }

Edge == { "MessageFlow_03ylhkh", "SequenceFlow_0z2xwql", "SequenceFlow_0uzla8o", "SequenceFlow_1fuwd1z", "SequenceFlow_0b7efwa", "SequenceFlow_0wto9d1", "SequenceFlow_01wc4ks", "SequenceFlow_0uplc1a", "SequenceFlow_03gudbc", "SequenceFlow_14kzfo3" }

Message == { "m1" }

msgtype ==
   "MessageFlow_03ylhkh" :> "m1"


source ==
   "MessageFlow_03ylhkh" :> "Task_1rt44mz"
@@ "SequenceFlow_0z2xwql" :> "StartEvent_1"
@@ "SequenceFlow_0uzla8o" :> "Task_1rt44mz"
@@ "SequenceFlow_1fuwd1z" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0b7efwa" :> "Task_1eirt50"
@@ "SequenceFlow_0wto9d1" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_01wc4ks" :> "Task_097548f"
@@ "SequenceFlow_0uplc1a" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_03gudbc" :> "Task_18t09mk"
@@ "SequenceFlow_14kzfo3" :> "StartEvent_1wwcoxd"

target ==
   "MessageFlow_03ylhkh" :> "Task_18t09mk"
@@ "SequenceFlow_0z2xwql" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0uzla8o" :> "EndEvent_0v9lt5i"
@@ "SequenceFlow_1fuwd1z" :> "Task_1rt44mz"
@@ "SequenceFlow_0b7efwa" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0wto9d1" :> "Task_1eirt50"
@@ "SequenceFlow_01wc4ks" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0uplc1a" :> "Task_097548f"
@@ "SequenceFlow_03gudbc" :> "EndEvent_1wbcvef"
@@ "SequenceFlow_14kzfo3" :> "Task_18t09mk"

CatN ==
   "A_" :> Process
@@ "B_" :> Process
@@ "Task_097548f" :> AbstractTask
@@ "Task_1eirt50" :> AbstractTask
@@ "ExclusiveGateway_0079typ" :> ExclusiveOr
@@ "EndEvent_0v9lt5i" :> NoneEndEvent
@@ "ExclusiveGateway_1j1chqb" :> Parallel
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_1rt44mz" :> SendTask
@@ "StartEvent_1wwcoxd" :> NoneStartEvent
@@ "EndEvent_1wbcvef" :> NoneEndEvent
@@ "Task_18t09mk" :> ReceiveTask

CatE ==
   "MessageFlow_03ylhkh" :> MessageFlow
@@ "SequenceFlow_0z2xwql" :> NormalSeqFlow
@@ "SequenceFlow_0uzla8o" :> NormalSeqFlow
@@ "SequenceFlow_1fuwd1z" :> NormalSeqFlow
@@ "SequenceFlow_0b7efwa" :> NormalSeqFlow
@@ "SequenceFlow_0wto9d1" :> NormalSeqFlow
@@ "SequenceFlow_01wc4ks" :> NormalSeqFlow
@@ "SequenceFlow_0uplc1a" :> NormalSeqFlow
@@ "SequenceFlow_03gudbc" :> NormalSeqFlow
@@ "SequenceFlow_14kzfo3" :> NormalSeqFlow

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

