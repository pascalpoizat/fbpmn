---------------- MODULE e009CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_1" :> { "Task_097548f", "Task_1eirt50", "ExclusiveGateway_0079typ", "EndEvent_0v9lt5i", "ExclusiveGateway_1j1chqb", "StartEvent_1", "Task_1rt44mz" }
  @@ "Process_1exocbo" :> { "StartEvent_1wwcoxd", "EndEvent_1wbcvef", "Task_18t09mk" }

Node == {
  "Process_1","Process_1exocbo","Task_097548f","Task_1eirt50","ExclusiveGateway_0079typ","EndEvent_0v9lt5i","ExclusiveGateway_1j1chqb","StartEvent_1","Task_1rt44mz","StartEvent_1wwcoxd","EndEvent_1wbcvef","Task_18t09mk"
}

Edge == {
  "MessageFlow_03ylhkh","SequenceFlow_0uplc1a","SequenceFlow_01wc4ks","SequenceFlow_0wto9d1","SequenceFlow_0b7efwa","SequenceFlow_1fuwd1z","SequenceFlow_0uzla8o","SequenceFlow_0z2xwql","SequenceFlow_14kzfo3","SequenceFlow_03gudbc"
}

Message == { "m1" }

msgtype ==
      "MessageFlow_03ylhkh" :> "m1"

source ==
   "MessageFlow_03ylhkh" :> "Task_1rt44mz"
@@ "SequenceFlow_0uplc1a" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_01wc4ks" :> "Task_097548f"
@@ "SequenceFlow_0wto9d1" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0b7efwa" :> "Task_1eirt50"
@@ "SequenceFlow_1fuwd1z" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0uzla8o" :> "Task_1rt44mz"
@@ "SequenceFlow_0z2xwql" :> "StartEvent_1"
@@ "SequenceFlow_14kzfo3" :> "StartEvent_1wwcoxd"
@@ "SequenceFlow_03gudbc" :> "Task_18t09mk"

target ==
   "MessageFlow_03ylhkh" :> "Task_18t09mk"
@@ "SequenceFlow_0uplc1a" :> "Task_097548f"
@@ "SequenceFlow_01wc4ks" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0wto9d1" :> "Task_1eirt50"
@@ "SequenceFlow_0b7efwa" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_1fuwd1z" :> "Task_1rt44mz"
@@ "SequenceFlow_0uzla8o" :> "EndEvent_0v9lt5i"
@@ "SequenceFlow_0z2xwql" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_14kzfo3" :> "Task_18t09mk"
@@ "SequenceFlow_03gudbc" :> "EndEvent_1wbcvef"

CatN ==
   "Process_1" :> Process
@@ "Process_1exocbo" :> Process
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
@@ "SequenceFlow_0uplc1a" :> NormalSeqFlow
@@ "SequenceFlow_01wc4ks" :> NormalSeqFlow
@@ "SequenceFlow_0wto9d1" :> NormalSeqFlow
@@ "SequenceFlow_0b7efwa" :> NormalSeqFlow
@@ "SequenceFlow_1fuwd1z" :> NormalSeqFlow
@@ "SequenceFlow_0uzla8o" :> NormalSeqFlow
@@ "SequenceFlow_0z2xwql" :> NormalSeqFlow
@@ "SequenceFlow_14kzfo3" :> NormalSeqFlow
@@ "SequenceFlow_03gudbc" :> NormalSeqFlow

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

INSTANCE PWSSemantics

================================================================

