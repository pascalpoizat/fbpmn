---------------- MODULE _010CheckTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_A" :> { "SP", "StartEvent_0ayuyd2", "EndEvent_0ns8te3" }
  @@ "Process_B" :> { "EndEvent_1s2d234", "StartEvent_13qwxem", "ReceiveTask_0tuz5r7" }
  @@ "SP" :> { "EndEvent_0v9lt5i", "Task_1eirt50", "Task_097548f", "ExclusiveGateway_1j1chqb", "StartEvent_1", "ExclusiveGateway_0079typ", "Task_1rt44mz" }

Node == {
  "Process_A","Process_B","SP","StartEvent_0ayuyd2","EndEvent_0ns8te3","EndEvent_0v9lt5i","Task_1eirt50","Task_097548f","ExclusiveGateway_1j1chqb","StartEvent_1","ExclusiveGateway_0079typ","Task_1rt44mz","EndEvent_1s2d234","StartEvent_13qwxem","ReceiveTask_0tuz5r7"
}

Edge == {
  "mf1","SequenceFlow_00aes3w","SequenceFlow_1vue23p","SequenceFlow_0z2xwql","SequenceFlow_0wto9d1","SequenceFlow_0uplc1a","SequenceFlow_01wc4ks","SequenceFlow_0b7efwa","SequenceFlow_1fuwd1z","SequenceFlow_0uzla8o","SequenceFlow_1rma85g","SequenceFlow_0ehu3gz"
}

Message == { "m1" }

msgtype ==
      "mf1" :> "m1"

source ==
   "mf1" :> "Task_1rt44mz"
@@ "SequenceFlow_00aes3w" :> "SP"
@@ "SequenceFlow_1vue23p" :> "StartEvent_0ayuyd2"
@@ "SequenceFlow_0z2xwql" :> "StartEvent_1"
@@ "SequenceFlow_0wto9d1" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0uplc1a" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_01wc4ks" :> "Task_097548f"
@@ "SequenceFlow_0b7efwa" :> "Task_1eirt50"
@@ "SequenceFlow_1fuwd1z" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0uzla8o" :> "Task_1rt44mz"
@@ "SequenceFlow_1rma85g" :> "StartEvent_13qwxem"
@@ "SequenceFlow_0ehu3gz" :> "ReceiveTask_0tuz5r7"

target ==
   "mf1" :> "ReceiveTask_0tuz5r7"
@@ "SequenceFlow_00aes3w" :> "EndEvent_0ns8te3"
@@ "SequenceFlow_1vue23p" :> "SP"
@@ "SequenceFlow_0z2xwql" :> "ExclusiveGateway_1j1chqb"
@@ "SequenceFlow_0wto9d1" :> "Task_1eirt50"
@@ "SequenceFlow_0uplc1a" :> "Task_097548f"
@@ "SequenceFlow_01wc4ks" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_0b7efwa" :> "ExclusiveGateway_0079typ"
@@ "SequenceFlow_1fuwd1z" :> "Task_1rt44mz"
@@ "SequenceFlow_0uzla8o" :> "EndEvent_0v9lt5i"
@@ "SequenceFlow_1rma85g" :> "ReceiveTask_0tuz5r7"
@@ "SequenceFlow_0ehu3gz" :> "EndEvent_1s2d234"

CatN ==
   "Process_A" :> Process
@@ "Process_B" :> Process
@@ "SP" :> SubProcess
@@ "StartEvent_0ayuyd2" :> NoneStartEvent
@@ "EndEvent_0ns8te3" :> NoneEndEvent
@@ "EndEvent_0v9lt5i" :> NoneEndEvent
@@ "Task_1eirt50" :> AbstractTask
@@ "Task_097548f" :> AbstractTask
@@ "ExclusiveGateway_1j1chqb" :> Parallel
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_0079typ" :> ExclusiveOr
@@ "Task_1rt44mz" :> SendTask
@@ "EndEvent_1s2d234" :> NoneEndEvent
@@ "StartEvent_13qwxem" :> NoneStartEvent
@@ "ReceiveTask_0tuz5r7" :> ReceiveTask

CatE ==
   "mf1" :> MsgFlow
@@ "SequenceFlow_00aes3w" :> NormalSeqFlow
@@ "SequenceFlow_1vue23p" :> NormalSeqFlow
@@ "SequenceFlow_0z2xwql" :> NormalSeqFlow
@@ "SequenceFlow_0wto9d1" :> NormalSeqFlow
@@ "SequenceFlow_0uplc1a" :> NormalSeqFlow
@@ "SequenceFlow_01wc4ks" :> NormalSeqFlow
@@ "SequenceFlow_0b7efwa" :> NormalSeqFlow
@@ "SequenceFlow_1fuwd1z" :> NormalSeqFlow
@@ "SequenceFlow_0uzla8o" :> NormalSeqFlow
@@ "SequenceFlow_1rma85g" :> NormalSeqFlow
@@ "SequenceFlow_0ehu3gz" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

