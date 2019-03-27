---------------- MODULE e021MBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "P_id" :> { "EndEvent_1hytbgh", "Task_06osngf", "EndEvent_112jhwq", "SubProcess_07e2e99", "StartEvent_1", "BoundaryEvent_1fak9ar", "BoundaryEvent_1q0fgiw" }
  @@ "Q_id" :> { "StartEvent_1jxrjjb", "ExclusiveGateway_0pvsvob", "ExclusiveGateway_1vvyptg", "EndEvent_1gf9mha", "Task_0ouyduq", "Task_0z3cxl5" }
  @@ "SubProcess_07e2e99" :> { "StartEvent_03bqw0j", "Task_1i35ppr", "Task_1kso3jk", "ExclusiveGateway_0hzcbkt", "ExclusiveGateway_1hukmk5", "EndEvent_0ovxd43" }

Node == {
  "P_id","Q_id","EndEvent_1hytbgh","Task_06osngf","EndEvent_112jhwq","SubProcess_07e2e99","StartEvent_1","BoundaryEvent_1fak9ar","BoundaryEvent_1q0fgiw","StartEvent_03bqw0j","Task_1i35ppr","Task_1kso3jk","ExclusiveGateway_0hzcbkt","ExclusiveGateway_1hukmk5","EndEvent_0ovxd43","StartEvent_1jxrjjb","ExclusiveGateway_0pvsvob","ExclusiveGateway_1vvyptg","EndEvent_1gf9mha","Task_0ouyduq","Task_0z3cxl5"
}

Edge == {
  "MessageFlow_01dn8b3","MessageFlow_1fv5g0n","SequenceFlow_109652j","SequenceFlow_0y8q6ot","SequenceFlow_1sp2uu5","SequenceFlow_1ag4q25","SequenceFlow_1rnwbjb","SequenceFlow_16cdiue","SequenceFlow_18dl2c1","SequenceFlow_00h8rbi","SequenceFlow_03zwnxj","SequenceFlow_0fcn4he","SequenceFlow_0e70fm8","SequenceFlow_1xvizyy","SequenceFlow_17254s0","SequenceFlow_08qsdvs","SequenceFlow_06cnlpk","SequenceFlow_0axwuh9","SequenceFlow_1es2p0l"
}

Message == { "msg1", "msg2" }

msgtype ==
      "MessageFlow_01dn8b3" :> "msg1"
  @@ "MessageFlow_1fv5g0n" :> "msg2"

source ==
   "MessageFlow_01dn8b3" :> "Task_0ouyduq"
@@ "MessageFlow_1fv5g0n" :> "Task_0z3cxl5"
@@ "SequenceFlow_109652j" :> "BoundaryEvent_1fak9ar"
@@ "SequenceFlow_0y8q6ot" :> "Task_06osngf"
@@ "SequenceFlow_1sp2uu5" :> "BoundaryEvent_1q0fgiw"
@@ "SequenceFlow_1ag4q25" :> "SubProcess_07e2e99"
@@ "SequenceFlow_1rnwbjb" :> "StartEvent_1"
@@ "SequenceFlow_16cdiue" :> "StartEvent_03bqw0j"
@@ "SequenceFlow_18dl2c1" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_00h8rbi" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_03zwnxj" :> "Task_1i35ppr"
@@ "SequenceFlow_0fcn4he" :> "Task_1kso3jk"
@@ "SequenceFlow_0e70fm8" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_1xvizyy" :> "ExclusiveGateway_1vvyptg"
@@ "SequenceFlow_17254s0" :> "Task_0z3cxl5"
@@ "SequenceFlow_08qsdvs" :> "Task_0ouyduq"
@@ "SequenceFlow_06cnlpk" :> "ExclusiveGateway_0pvsvob"
@@ "SequenceFlow_0axwuh9" :> "ExclusiveGateway_0pvsvob"
@@ "SequenceFlow_1es2p0l" :> "StartEvent_1jxrjjb"

target ==
   "MessageFlow_01dn8b3" :> "BoundaryEvent_1q0fgiw"
@@ "MessageFlow_1fv5g0n" :> "BoundaryEvent_1fak9ar"
@@ "SequenceFlow_109652j" :> "Task_06osngf"
@@ "SequenceFlow_0y8q6ot" :> "EndEvent_112jhwq"
@@ "SequenceFlow_1sp2uu5" :> "EndEvent_1hytbgh"
@@ "SequenceFlow_1ag4q25" :> "EndEvent_1hytbgh"
@@ "SequenceFlow_1rnwbjb" :> "SubProcess_07e2e99"
@@ "SequenceFlow_16cdiue" :> "ExclusiveGateway_1hukmk5"
@@ "SequenceFlow_18dl2c1" :> "Task_1i35ppr"
@@ "SequenceFlow_00h8rbi" :> "Task_1kso3jk"
@@ "SequenceFlow_03zwnxj" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_0fcn4he" :> "ExclusiveGateway_0hzcbkt"
@@ "SequenceFlow_0e70fm8" :> "EndEvent_0ovxd43"
@@ "SequenceFlow_1xvizyy" :> "EndEvent_1gf9mha"
@@ "SequenceFlow_17254s0" :> "ExclusiveGateway_1vvyptg"
@@ "SequenceFlow_08qsdvs" :> "ExclusiveGateway_1vvyptg"
@@ "SequenceFlow_06cnlpk" :> "Task_0z3cxl5"
@@ "SequenceFlow_0axwuh9" :> "Task_0ouyduq"
@@ "SequenceFlow_1es2p0l" :> "ExclusiveGateway_0pvsvob"

CatN ==
   "P_id" :> Process
@@ "Q_id" :> Process
@@ "EndEvent_1hytbgh" :> NoneEndEvent
@@ "Task_06osngf" :> AbstractTask
@@ "EndEvent_112jhwq" :> NoneEndEvent
@@ "SubProcess_07e2e99" :> SubProcess
@@ "StartEvent_1" :> NoneStartEvent
@@ "BoundaryEvent_1fak9ar" :> MessageBoundaryEvent
@@ "BoundaryEvent_1q0fgiw" :> MessageBoundaryEvent
@@ "StartEvent_03bqw0j" :> NoneStartEvent
@@ "Task_1i35ppr" :> AbstractTask
@@ "Task_1kso3jk" :> AbstractTask
@@ "ExclusiveGateway_0hzcbkt" :> ExclusiveOr
@@ "ExclusiveGateway_1hukmk5" :> ExclusiveOr
@@ "EndEvent_0ovxd43" :> NoneEndEvent
@@ "StartEvent_1jxrjjb" :> NoneStartEvent
@@ "ExclusiveGateway_0pvsvob" :> ExclusiveOr
@@ "ExclusiveGateway_1vvyptg" :> ExclusiveOr
@@ "EndEvent_1gf9mha" :> NoneEndEvent
@@ "Task_0ouyduq" :> SendTask
@@ "Task_0z3cxl5" :> SendTask

CatE ==
   "MessageFlow_01dn8b3" :> MessageFlow
@@ "MessageFlow_1fv5g0n" :> MessageFlow
@@ "SequenceFlow_109652j" :> NormalSeqFlow
@@ "SequenceFlow_0y8q6ot" :> NormalSeqFlow
@@ "SequenceFlow_1sp2uu5" :> NormalSeqFlow
@@ "SequenceFlow_1ag4q25" :> NormalSeqFlow
@@ "SequenceFlow_1rnwbjb" :> NormalSeqFlow
@@ "SequenceFlow_16cdiue" :> NormalSeqFlow
@@ "SequenceFlow_18dl2c1" :> ConditionalSeqFlow
@@ "SequenceFlow_00h8rbi" :> DefaultSeqFlow
@@ "SequenceFlow_03zwnxj" :> NormalSeqFlow
@@ "SequenceFlow_0fcn4he" :> NormalSeqFlow
@@ "SequenceFlow_0e70fm8" :> NormalSeqFlow
@@ "SequenceFlow_1xvizyy" :> NormalSeqFlow
@@ "SequenceFlow_17254s0" :> NormalSeqFlow
@@ "SequenceFlow_08qsdvs" :> NormalSeqFlow
@@ "SequenceFlow_06cnlpk" :> DefaultSeqFlow
@@ "SequenceFlow_0axwuh9" :> ConditionalSeqFlow
@@ "SequenceFlow_1es2p0l" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

cancelActivity ==
   "BoundaryEvent_1q0fgiw" :> TRUE
@@ "BoundaryEvent_1fak9ar" :> FALSE

attachedTo ==
   "BoundaryEvent_1q0fgiw" :> "SubProcess_07e2e99"
@@ "BoundaryEvent_1fak9ar" :> "SubProcess_07e2e99"

WF == INSTANCE PWSWellFormed
ASSUME WF!WellTyped
ASSUME WF!WellFormedness

ConstraintNode == TRUE \* none
ConstraintEdge == TRUE \* none
Constraint == TRUE     \* none
INSTANCE PWSConstraints

INSTANCE PWSSemantics

================================================================

