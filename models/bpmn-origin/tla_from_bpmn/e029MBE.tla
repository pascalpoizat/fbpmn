---------------- MODULE e029MBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> { "msg1", "msg2" }
  @@ "Q_" :> { "msg3" }

ContainRel ==
  "P_" :> { "SubProcess_07e2e99", "StartEvent_1", "EndEvent_1hytbgh", "Task_06osngf", "EndEvent_112jhwq", "BoundaryEvent_1fak9ar", "BoundaryEvent_1q0fgiw" }
  @@ "Q_" :> { "SubProcess_0joqwjm", "StartEvent_1jxrjjb", "EndEvent_1gf9mha", "BoundaryEvent_0k5p91i" }
  @@ "SubProcess_07e2e99" :> { "StartEvent_03bqw0j", "Task_1i35ppr", "Task_1kso3jk", "ExclusiveGateway_0hzcbkt", "ExclusiveGateway_1hukmk5", "EndEvent_0ovxd43" }
  @@ "SubProcess_0joqwjm" :> { "ExclusiveGateway_0pvsvob", "ExclusiveGateway_1vvyptg", "Task_0ouyduq", "Task_0z3cxl5", "StartEvent_0ef0xw9", "EndEvent_1whel54" }

Node == { "P_", "Q_", "SubProcess_07e2e99", "StartEvent_1", "EndEvent_1hytbgh", "Task_06osngf", "EndEvent_112jhwq", "BoundaryEvent_1fak9ar", "BoundaryEvent_1q0fgiw", "StartEvent_03bqw0j", "Task_1i35ppr", "Task_1kso3jk", "ExclusiveGateway_0hzcbkt", "ExclusiveGateway_1hukmk5", "EndEvent_0ovxd43", "SubProcess_0joqwjm", "StartEvent_1jxrjjb", "EndEvent_1gf9mha", "BoundaryEvent_0k5p91i", "ExclusiveGateway_0pvsvob", "ExclusiveGateway_1vvyptg", "Task_0ouyduq", "Task_0z3cxl5", "StartEvent_0ef0xw9", "EndEvent_1whel54" }

Edge == { "MessageFlow_01dn8b3", "MessageFlow_1fv5g0n", "MessageFlow_01rg2pg", "SequenceFlow_1rnwbjb", "SequenceFlow_1ag4q25", "SequenceFlow_1sp2uu5", "SequenceFlow_0y8q6ot", "SequenceFlow_109652j", "SequenceFlow_16cdiue", "SequenceFlow_18dl2c1", "SequenceFlow_00h8rbi", "SequenceFlow_03zwnxj", "SequenceFlow_0fcn4he", "SequenceFlow_0e70fm8", "SequenceFlow_1hqd2qa", "SequenceFlow_1es2p0l", "SequenceFlow_1xvizyy", "SequenceFlow_06cnlpk", "SequenceFlow_0axwuh9", "SequenceFlow_17254s0", "SequenceFlow_08qsdvs", "SequenceFlow_1i24zsv", "SequenceFlow_1hr9yu6" }

Message == { "msg1", "msg2", "msg3" }

msgtype ==
   "MessageFlow_01dn8b3" :> "msg1"
@@ "MessageFlow_1fv5g0n" :> "msg2"
@@ "MessageFlow_01rg2pg" :> "msg3"


source ==
   "MessageFlow_01dn8b3" :> "Task_0ouyduq"
@@ "MessageFlow_1fv5g0n" :> "Task_0z3cxl5"
@@ "MessageFlow_01rg2pg" :> "EndEvent_0ovxd43"
@@ "SequenceFlow_1rnwbjb" :> "StartEvent_1"
@@ "SequenceFlow_1ag4q25" :> "SubProcess_07e2e99"
@@ "SequenceFlow_1sp2uu5" :> "BoundaryEvent_1q0fgiw"
@@ "SequenceFlow_0y8q6ot" :> "Task_06osngf"
@@ "SequenceFlow_109652j" :> "BoundaryEvent_1fak9ar"
@@ "SequenceFlow_16cdiue" :> "StartEvent_03bqw0j"
@@ "SequenceFlow_18dl2c1" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_00h8rbi" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_03zwnxj" :> "Task_1i35ppr"
@@ "SequenceFlow_0fcn4he" :> "Task_1kso3jk"
@@ "SequenceFlow_0e70fm8" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_1hqd2qa" :> "BoundaryEvent_0k5p91i"
@@ "SequenceFlow_1es2p0l" :> "StartEvent_1jxrjjb"
@@ "SequenceFlow_1xvizyy" :> "SubProcess_0joqwjm"
@@ "SequenceFlow_06cnlpk" :> "ExclusiveGateway_0pvsvob"
@@ "SequenceFlow_0axwuh9" :> "ExclusiveGateway_0pvsvob"
@@ "SequenceFlow_17254s0" :> "Task_0z3cxl5"
@@ "SequenceFlow_08qsdvs" :> "Task_0ouyduq"
@@ "SequenceFlow_1i24zsv" :> "StartEvent_0ef0xw9"
@@ "SequenceFlow_1hr9yu6" :> "ExclusiveGateway_1vvyptg"

target ==
   "MessageFlow_01dn8b3" :> "BoundaryEvent_1q0fgiw"
@@ "MessageFlow_1fv5g0n" :> "BoundaryEvent_1fak9ar"
@@ "MessageFlow_01rg2pg" :> "BoundaryEvent_0k5p91i"
@@ "SequenceFlow_1rnwbjb" :> "SubProcess_07e2e99"
@@ "SequenceFlow_1ag4q25" :> "EndEvent_1hytbgh"
@@ "SequenceFlow_1sp2uu5" :> "EndEvent_1hytbgh"
@@ "SequenceFlow_0y8q6ot" :> "EndEvent_112jhwq"
@@ "SequenceFlow_109652j" :> "Task_06osngf"
@@ "SequenceFlow_16cdiue" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_18dl2c1" :> "Task_1i35ppr"
@@ "SequenceFlow_00h8rbi" :> "Task_1kso3jk"
@@ "SequenceFlow_03zwnxj" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_0fcn4he" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_0e70fm8" :> "EndEvent_0ovxd43"
@@ "SequenceFlow_1hqd2qa" :> "EndEvent_1gf9mha"
@@ "SequenceFlow_1es2p0l" :> "SubProcess_0joqwjm"
@@ "SequenceFlow_1xvizyy" :> "EndEvent_1gf9mha"
@@ "SequenceFlow_06cnlpk" :> "Task_0z3cxl5"
@@ "SequenceFlow_0axwuh9" :> "Task_0ouyduq"
@@ "SequenceFlow_17254s0" :> "ExclusiveGateway_1vvyptg"
@@ "SequenceFlow_08qsdvs" :> "ExclusiveGateway_1vvyptg"
@@ "SequenceFlow_1i24zsv" :> "ExclusiveGateway_0pvsvob"
@@ "SequenceFlow_1hr9yu6" :> "EndEvent_1whel54"

CatN ==
   "P_" :> Process
@@ "Q_" :> Process
@@ "SubProcess_07e2e99" :> SubProcess
@@ "StartEvent_1" :> NoneStartEvent
@@ "EndEvent_1hytbgh" :> NoneEndEvent
@@ "Task_06osngf" :> AbstractTask
@@ "EndEvent_112jhwq" :> NoneEndEvent
@@ "BoundaryEvent_1fak9ar" :> MessageBoundaryEvent
@@ "BoundaryEvent_1q0fgiw" :> MessageBoundaryEvent
@@ "StartEvent_03bqw0j" :> NoneStartEvent
@@ "Task_1i35ppr" :> AbstractTask
@@ "Task_1kso3jk" :> AbstractTask
@@ "ExclusiveGateway_0hzcbkt" :> ExclusiveOr
@@ "ExclusiveGateway_1hukmk5" :> ExclusiveOr
@@ "EndEvent_0ovxd43" :> MessageEndEvent
@@ "SubProcess_0joqwjm" :> SubProcess
@@ "StartEvent_1jxrjjb" :> NoneStartEvent
@@ "EndEvent_1gf9mha" :> NoneEndEvent
@@ "BoundaryEvent_0k5p91i" :> MessageBoundaryEvent
@@ "ExclusiveGateway_0pvsvob" :> ExclusiveOr
@@ "ExclusiveGateway_1vvyptg" :> ExclusiveOr
@@ "Task_0ouyduq" :> SendTask
@@ "Task_0z3cxl5" :> SendTask
@@ "StartEvent_0ef0xw9" :> NoneStartEvent
@@ "EndEvent_1whel54" :> NoneEndEvent

CatE ==
   "MessageFlow_01dn8b3" :> MessageFlow
@@ "MessageFlow_1fv5g0n" :> MessageFlow
@@ "MessageFlow_01rg2pg" :> MessageFlow
@@ "SequenceFlow_1rnwbjb" :> NormalSeqFlow
@@ "SequenceFlow_1ag4q25" :> NormalSeqFlow
@@ "SequenceFlow_1sp2uu5" :> NormalSeqFlow
@@ "SequenceFlow_0y8q6ot" :> NormalSeqFlow
@@ "SequenceFlow_109652j" :> NormalSeqFlow
@@ "SequenceFlow_16cdiue" :> NormalSeqFlow
@@ "SequenceFlow_18dl2c1" :> ConditionalSeqFlow
@@ "SequenceFlow_00h8rbi" :> DefaultSeqFlow
@@ "SequenceFlow_03zwnxj" :> NormalSeqFlow
@@ "SequenceFlow_0fcn4he" :> NormalSeqFlow
@@ "SequenceFlow_0e70fm8" :> NormalSeqFlow
@@ "SequenceFlow_1hqd2qa" :> NormalSeqFlow
@@ "SequenceFlow_1es2p0l" :> NormalSeqFlow
@@ "SequenceFlow_1xvizyy" :> NormalSeqFlow
@@ "SequenceFlow_06cnlpk" :> DefaultSeqFlow
@@ "SequenceFlow_0axwuh9" :> ConditionalSeqFlow
@@ "SequenceFlow_17254s0" :> NormalSeqFlow
@@ "SequenceFlow_08qsdvs" :> NormalSeqFlow
@@ "SequenceFlow_1i24zsv" :> NormalSeqFlow
@@ "SequenceFlow_1hr9yu6" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_1fak9ar" :> [ attachedTo |-> "SubProcess_07e2e99", cancelActivity |-> TRUE ]
@@ "BoundaryEvent_1q0fgiw" :> [ attachedTo |-> "SubProcess_07e2e99", cancelActivity |-> TRUE ]
@@ "BoundaryEvent_0k5p91i" :> [ attachedTo |-> "SubProcess_0joqwjm", cancelActivity |-> TRUE ]

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

