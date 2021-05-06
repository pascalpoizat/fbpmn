---------------- MODULE e011CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "A_" :> {  }
  @@ "B_" :> { "m1" }

ContainRel ==
  "A_" :> { "SP", "StartEvent_0ayuyd2", "SendTask_0vp135q", "EndEvent_0ns8te3" }
  @@ "B_" :> { "EndEvent_1s2d234", "StartEvent_13qwxem", "ReceiveTask_0tuz5r7" }
  @@ "SP" :> { "EndEvent_0v9lt5i", "Task_1eirt50", "Task_097548f", "ExclusiveGateway_1j1chqb", "StartEvent_1", "ExclusiveGateway_0079typ" }

Node == { "A_", "B_", "SP", "StartEvent_0ayuyd2", "SendTask_0vp135q", "EndEvent_0ns8te3", "EndEvent_0v9lt5i", "Task_1eirt50", "Task_097548f", "ExclusiveGateway_1j1chqb", "StartEvent_1", "ExclusiveGateway_0079typ", "EndEvent_1s2d234", "StartEvent_13qwxem", "ReceiveTask_0tuz5r7" }

Edge == { "mf1", "SequenceFlow_10xxs5u", "SequenceFlow_1vue23p", "SequenceFlow_00aes3w", "SequenceFlow_0z2xwql", "SequenceFlow_0wto9d1", "SequenceFlow_0uplc1a", "SequenceFlow_01wc4ks", "SequenceFlow_0b7efwa", "SequenceFlow_1fuwd1z", "SequenceFlow_0ehu3gz", "SequenceFlow_1rma85g" }

Message == { "m1" }

msgtype ==
   "mf1" :> "m1"


source ==
   "mf1" :> "SendTask_0vp135q"
@@ "SequenceFlow_10xxs5u" :> "SP"
@@ "SequenceFlow_1vue23p" :> "StartEvent_0ayuyd2"
@@ "SequenceFlow_00aes3w" :> "SendTask_0vp135q"
@@ "SequenceFlow_0z2xwql" :> "StartEvent_1"
@@ "SequenceFlow_0wto9d1" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0uplc1a" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_01wc4ks" :> "Task_097548f"
@@ "SequenceFlow_0b7efwa" :> "Task_1eirt50"
@@ "SequenceFlow_1fuwd1z" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0ehu3gz" :> "ReceiveTask_0tuz5r7"
@@ "SequenceFlow_1rma85g" :> "StartEvent_13qwxem"

target ==
   "mf1" :> "ReceiveTask_0tuz5r7"
@@ "SequenceFlow_10xxs5u" :> "SendTask_0vp135q"
@@ "SequenceFlow_1vue23p" :> "SP"
@@ "SequenceFlow_00aes3w" :> "EndEvent_0ns8te3"
@@ "SequenceFlow_0z2xwql" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0wto9d1" :> "Task_1eirt50"
@@ "SequenceFlow_0uplc1a" :> "Task_097548f"
@@ "SequenceFlow_01wc4ks" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0b7efwa" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_1fuwd1z" :> "EndEvent_0v9lt5i"
@@ "SequenceFlow_0ehu3gz" :> "EndEvent_1s2d234"
@@ "SequenceFlow_1rma85g" :> "ReceiveTask_0tuz5r7"

CatN ==
   "A_" :> Process
@@ "B_" :> Process
@@ "SP" :> SubProcess
@@ "StartEvent_0ayuyd2" :> NoneStartEvent
@@ "SendTask_0vp135q" :> SendTask
@@ "EndEvent_0ns8te3" :> NoneEndEvent
@@ "EndEvent_0v9lt5i" :> NoneEndEvent
@@ "Task_1eirt50" :> AbstractTask
@@ "Task_097548f" :> AbstractTask
@@ "ExclusiveGateway_1j1chqb" :> Parallel
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_0079typ" :> ExclusiveOr
@@ "EndEvent_1s2d234" :> NoneEndEvent
@@ "StartEvent_13qwxem" :> NoneStartEvent
@@ "ReceiveTask_0tuz5r7" :> ReceiveTask

CatE ==
   "mf1" :> MessageFlow
@@ "SequenceFlow_10xxs5u" :> NormalSeqFlow
@@ "SequenceFlow_1vue23p" :> NormalSeqFlow
@@ "SequenceFlow_00aes3w" :> NormalSeqFlow
@@ "SequenceFlow_0z2xwql" :> NormalSeqFlow
@@ "SequenceFlow_0wto9d1" :> NormalSeqFlow
@@ "SequenceFlow_0uplc1a" :> NormalSeqFlow
@@ "SequenceFlow_01wc4ks" :> NormalSeqFlow
@@ "SequenceFlow_0b7efwa" :> NormalSeqFlow
@@ "SequenceFlow_1fuwd1z" :> NormalSeqFlow
@@ "SequenceFlow_0ehu3gz" :> NormalSeqFlow
@@ "SequenceFlow_1rma85g" :> NormalSeqFlow

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

