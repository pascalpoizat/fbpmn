---------------- MODULE e008CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "A_" :> {  }

ContainRel ==
  "A_" :> { "SubProcess_0mgtdae", "StartEvent_0ayuyd2", "EndEvent_0ns8te3" }
  @@ "SubProcess_0mgtdae" :> { "EndEvent_0v9lt5i", "Task_1rt44mz", "Task_1eirt50", "Task_097548f", "ExclusiveGateway_1j1chqb", "StartEvent_1", "ExclusiveGateway_0079typ" }

Node == { "A_", "SubProcess_0mgtdae", "StartEvent_0ayuyd2", "EndEvent_0ns8te3", "EndEvent_0v9lt5i", "Task_1rt44mz", "Task_1eirt50", "Task_097548f", "ExclusiveGateway_1j1chqb", "StartEvent_1", "ExclusiveGateway_0079typ" }

Edge == { "SequenceFlow_00aes3w", "SequenceFlow_1vue23p", "SequenceFlow_0z2xwql", "SequenceFlow_0wto9d1", "SequenceFlow_0uplc1a", "SequenceFlow_01wc4ks", "SequenceFlow_0b7efwa", "SequenceFlow_1fuwd1z", "SequenceFlow_0uzla8o" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_00aes3w" :> "SubProcess_0mgtdae"
@@ "SequenceFlow_1vue23p" :> "StartEvent_0ayuyd2"
@@ "SequenceFlow_0z2xwql" :> "StartEvent_1"
@@ "SequenceFlow_0wto9d1" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0uplc1a" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_01wc4ks" :> "Task_097548f"
@@ "SequenceFlow_0b7efwa" :> "Task_1eirt50"
@@ "SequenceFlow_1fuwd1z" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0uzla8o" :> "Task_1rt44mz"

target ==
   "SequenceFlow_00aes3w" :> "EndEvent_0ns8te3"
@@ "SequenceFlow_1vue23p" :> "SubProcess_0mgtdae"
@@ "SequenceFlow_0z2xwql" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0wto9d1" :> "Task_1eirt50"
@@ "SequenceFlow_0uplc1a" :> "Task_097548f"
@@ "SequenceFlow_01wc4ks" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0b7efwa" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_1fuwd1z" :> "Task_1rt44mz"
@@ "SequenceFlow_0uzla8o" :> "EndEvent_0v9lt5i"

CatN ==
   "A_" :> Process
@@ "SubProcess_0mgtdae" :> SubProcess
@@ "StartEvent_0ayuyd2" :> NoneStartEvent
@@ "EndEvent_0ns8te3" :> NoneEndEvent
@@ "EndEvent_0v9lt5i" :> NoneEndEvent
@@ "Task_1rt44mz" :> AbstractTask
@@ "Task_1eirt50" :> AbstractTask
@@ "Task_097548f" :> AbstractTask
@@ "ExclusiveGateway_1j1chqb" :> Parallel
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_0079typ" :> ExclusiveOr

CatE ==
   "SequenceFlow_00aes3w" :> NormalSeqFlow
@@ "SequenceFlow_1vue23p" :> NormalSeqFlow
@@ "SequenceFlow_0z2xwql" :> NormalSeqFlow
@@ "SequenceFlow_0wto9d1" :> NormalSeqFlow
@@ "SequenceFlow_0uplc1a" :> NormalSeqFlow
@@ "SequenceFlow_01wc4ks" :> NormalSeqFlow
@@ "SequenceFlow_0b7efwa" :> NormalSeqFlow
@@ "SequenceFlow_1fuwd1z" :> NormalSeqFlow
@@ "SequenceFlow_0uzla8o" :> NormalSeqFlow

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

