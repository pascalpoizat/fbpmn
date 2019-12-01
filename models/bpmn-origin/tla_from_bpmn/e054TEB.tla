---------------- MODULE e054TEB ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_05gzdtd" :> {  }
  @@ "Process_104kmox" :> { "m1", "m2" }
  @@ "Process_12oxudf" :> {  }

ContainRel ==
  "Process_05gzdtd" :> { "StartEvent_0ng45ln", "ExclusiveGateway_0kvru56", "EndEvent_1jr9ymp", "EndEvent_1imvmci", "SendTask_1i6lsga", "Task_00w4wn4" }
  @@ "Process_104kmox" :> { "StartEvent_1xhyji9", "ExclusiveGateway_03wdh0i", "IntermediateCatchEvent_0v47yyg", "IntermediateCatchEvent_1ss52yx", "IntermediateCatchEvent_1krpoya", "EndEvent_0p6olxz", "EndEvent_1khaqp3", "EndEvent_06hq74j" }
  @@ "Process_12oxudf" :> { "EndEvent_0om01ac", "Task_0eo34vw", "StartEvent_1eicooe", "ExclusiveGateway_1ukkste", "EndEvent_1i50law", "Task_0cjmppv" }

Node == {
  "Process_104kmox","Process_05gzdtd","Process_12oxudf","StartEvent_1xhyji9","ExclusiveGateway_03wdh0i","IntermediateCatchEvent_0v47yyg","IntermediateCatchEvent_1ss52yx","IntermediateCatchEvent_1krpoya","EndEvent_0p6olxz","EndEvent_1khaqp3","EndEvent_06hq74j","StartEvent_0ng45ln","ExclusiveGateway_0kvru56","EndEvent_1jr9ymp","EndEvent_1imvmci","SendTask_1i6lsga","Task_00w4wn4","EndEvent_0om01ac","Task_0eo34vw","StartEvent_1eicooe","ExclusiveGateway_1ukkste","EndEvent_1i50law","Task_0cjmppv"
}

Edge == {
  "MessageFlow_0anis1g","MessageFlow_0mma6b7","SequenceFlow_02i9aub","SequenceFlow_1ejcjun","SequenceFlow_1lim0ak","SequenceFlow_0d4uo9u","SequenceFlow_01mi0z5","SequenceFlow_1w1q1tz","SequenceFlow_1kqxai7","SequenceFlow_0062gga","SequenceFlow_1fpdtzj","SequenceFlow_0m6s08w","SequenceFlow_1jusdil","SequenceFlow_0sz8f29","SequenceFlow_13q04ef","SequenceFlow_1jbid03","SequenceFlow_1qj818y","SequenceFlow_1lmhnxh","SequenceFlow_11z8969"
}

Message == { "m1", "m2" }

msgtype ==
      "MessageFlow_0anis1g" :> "m1"
  @@ "MessageFlow_0mma6b7" :> "m2"

source ==
   "MessageFlow_0anis1g" :> "Task_0cjmppv"
@@ "MessageFlow_0mma6b7" :> "Task_00w4wn4"
@@ "SequenceFlow_02i9aub" :> "StartEvent_1xhyji9"
@@ "SequenceFlow_1ejcjun" :> "ExclusiveGateway_03wdh0i"
@@ "SequenceFlow_1lim0ak" :> "ExclusiveGateway_03wdh0i"
@@ "SequenceFlow_0d4uo9u" :> "ExclusiveGateway_03wdh0i"
@@ "SequenceFlow_01mi0z5" :> "IntermediateCatchEvent_0v47yyg"
@@ "SequenceFlow_1w1q1tz" :> "IntermediateCatchEvent_1ss52yx"
@@ "SequenceFlow_1kqxai7" :> "IntermediateCatchEvent_1krpoya"
@@ "SequenceFlow_0062gga" :> "StartEvent_0ng45ln"
@@ "SequenceFlow_1fpdtzj" :> "ExclusiveGateway_0kvru56"
@@ "SequenceFlow_0m6s08w" :> "ExclusiveGateway_0kvru56"
@@ "SequenceFlow_1jusdil" :> "SendTask_1i6lsga"
@@ "SequenceFlow_0sz8f29" :> "Task_00w4wn4"
@@ "SequenceFlow_13q04ef" :> "ExclusiveGateway_1ukkste"
@@ "SequenceFlow_1jbid03" :> "Task_0cjmppv"
@@ "SequenceFlow_1qj818y" :> "ExclusiveGateway_1ukkste"
@@ "SequenceFlow_1lmhnxh" :> "StartEvent_1eicooe"
@@ "SequenceFlow_11z8969" :> "Task_0eo34vw"

target ==
   "MessageFlow_0anis1g" :> "IntermediateCatchEvent_0v47yyg"
@@ "MessageFlow_0mma6b7" :> "IntermediateCatchEvent_1ss52yx"
@@ "SequenceFlow_02i9aub" :> "ExclusiveGateway_03wdh0i"
@@ "SequenceFlow_1ejcjun" :> "IntermediateCatchEvent_0v47yyg"
@@ "SequenceFlow_1lim0ak" :> "IntermediateCatchEvent_1ss52yx"
@@ "SequenceFlow_0d4uo9u" :> "IntermediateCatchEvent_1krpoya"
@@ "SequenceFlow_01mi0z5" :> "EndEvent_0p6olxz"
@@ "SequenceFlow_1w1q1tz" :> "EndEvent_1khaqp3"
@@ "SequenceFlow_1kqxai7" :> "EndEvent_06hq74j"
@@ "SequenceFlow_0062gga" :> "ExclusiveGateway_0kvru56"
@@ "SequenceFlow_1fpdtzj" :> "SendTask_1i6lsga"
@@ "SequenceFlow_0m6s08w" :> "Task_00w4wn4"
@@ "SequenceFlow_1jusdil" :> "EndEvent_1jr9ymp"
@@ "SequenceFlow_0sz8f29" :> "EndEvent_1imvmci"
@@ "SequenceFlow_13q04ef" :> "Task_0cjmppv"
@@ "SequenceFlow_1jbid03" :> "EndEvent_0om01ac"
@@ "SequenceFlow_1qj818y" :> "Task_0eo34vw"
@@ "SequenceFlow_1lmhnxh" :> "ExclusiveGateway_1ukkste"
@@ "SequenceFlow_11z8969" :> "EndEvent_1i50law"

CatN ==
   "Process_104kmox" :> Process
@@ "Process_05gzdtd" :> Process
@@ "Process_12oxudf" :> Process
@@ "StartEvent_1xhyji9" :> NoneStartEvent
@@ "ExclusiveGateway_03wdh0i" :> EventBased
@@ "IntermediateCatchEvent_0v47yyg" :> CatchMessageIntermediateEvent
@@ "IntermediateCatchEvent_1ss52yx" :> CatchMessageIntermediateEvent
@@ "IntermediateCatchEvent_1krpoya" :> TimerIntermediateEvent
@@ "EndEvent_0p6olxz" :> NoneEndEvent
@@ "EndEvent_1khaqp3" :> NoneEndEvent
@@ "EndEvent_06hq74j" :> NoneEndEvent
@@ "StartEvent_0ng45ln" :> NoneStartEvent
@@ "ExclusiveGateway_0kvru56" :> ExclusiveOr
@@ "EndEvent_1jr9ymp" :> NoneEndEvent
@@ "EndEvent_1imvmci" :> NoneEndEvent
@@ "SendTask_1i6lsga" :> AbstractTask
@@ "Task_00w4wn4" :> SendTask
@@ "EndEvent_0om01ac" :> NoneEndEvent
@@ "Task_0eo34vw" :> AbstractTask
@@ "StartEvent_1eicooe" :> NoneStartEvent
@@ "ExclusiveGateway_1ukkste" :> ExclusiveOr
@@ "EndEvent_1i50law" :> NoneEndEvent
@@ "Task_0cjmppv" :> SendTask

CatE ==
   "MessageFlow_0anis1g" :> MessageFlow
@@ "MessageFlow_0mma6b7" :> MessageFlow
@@ "SequenceFlow_02i9aub" :> NormalSeqFlow
@@ "SequenceFlow_1ejcjun" :> NormalSeqFlow
@@ "SequenceFlow_1lim0ak" :> NormalSeqFlow
@@ "SequenceFlow_0d4uo9u" :> NormalSeqFlow
@@ "SequenceFlow_01mi0z5" :> NormalSeqFlow
@@ "SequenceFlow_1w1q1tz" :> NormalSeqFlow
@@ "SequenceFlow_1kqxai7" :> NormalSeqFlow
@@ "SequenceFlow_0062gga" :> NormalSeqFlow
@@ "SequenceFlow_1fpdtzj" :> NormalSeqFlow
@@ "SequenceFlow_0m6s08w" :> NormalSeqFlow
@@ "SequenceFlow_1jusdil" :> NormalSeqFlow
@@ "SequenceFlow_0sz8f29" :> NormalSeqFlow
@@ "SequenceFlow_13q04ef" :> NormalSeqFlow
@@ "SequenceFlow_1jbid03" :> NormalSeqFlow
@@ "SequenceFlow_1qj818y" :> NormalSeqFlow
@@ "SequenceFlow_1lmhnxh" :> NormalSeqFlow
@@ "SequenceFlow_11z8969" :> NormalSeqFlow

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

