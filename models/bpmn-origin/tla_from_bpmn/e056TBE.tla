---------------- MODULE e056TBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_0y7bmnu" :> { "m1", "m2" }
  @@ "Process_1" :> {  }

ContainRel ==
  "Process_0y7bmnu" :> { "StartEvent_1yq5hw0", "IntermediateCatchEvent_0ufeqmr", "IntermediateCatchEvent_14fmuo3", "EndEvent_1c69md6", "ExclusiveGateway_0nhvvs9", "ExclusiveGateway_0ngzdyp" }
  @@ "Process_1" :> { "SubProcess_1ggm3we", "IntermediateThrowEvent_0xxuh9e", "EndEvent_00diytc", "Task_05bgz5k", "StartEvent_1", "BoundaryEvent_1jast47", "EndEvent_0v2esc4" }
  @@ "SubProcess_1ggm3we" :> { "StartEvent_134yuce", "Task_1ljmp3l", "EndEvent_1ex5meo", "ExclusiveGateway_121v81s", "ExclusiveGateway_0chq45h" }

Node == { "Process_1", "Process_0y7bmnu", "SubProcess_1ggm3we", "IntermediateThrowEvent_0xxuh9e", "EndEvent_00diytc", "Task_05bgz5k", "StartEvent_1", "BoundaryEvent_1jast47", "EndEvent_0v2esc4", "StartEvent_134yuce", "Task_1ljmp3l", "EndEvent_1ex5meo", "ExclusiveGateway_121v81s", "ExclusiveGateway_0chq45h", "StartEvent_1yq5hw0", "IntermediateCatchEvent_0ufeqmr", "IntermediateCatchEvent_14fmuo3", "EndEvent_1c69md6", "ExclusiveGateway_0nhvvs9", "ExclusiveGateway_0ngzdyp" }

Edge == { "MessageFlow_1295wps", "MessageFlow_13dqcc0", "SequenceFlow_034nt5z", "SequenceFlow_1oxtfj2", "SequenceFlow_1yblldx", "SequenceFlow_0dyhbe0", "SequenceFlow_1aj35wd", "SequenceFlow_1hxg2dl", "SequenceFlow_0efj6hj", "SequenceFlow_06wfm19", "SequenceFlow_029fmhs", "SequenceFlow_19jmp5d", "SequenceFlow_01hgmep", "SequenceFlow_1fut9qx", "SequenceFlow_19ixkyb", "SequenceFlow_1k7hxgw", "SequenceFlow_0s6c8vn", "SequenceFlow_13vx7cl" }

Message == { "m1", "m2" }

msgtype ==
   "MessageFlow_1295wps" :> "m1"
@@ "MessageFlow_13dqcc0" :> "m2"


source ==
   "MessageFlow_1295wps" :> "Task_05bgz5k"
@@ "MessageFlow_13dqcc0" :> "IntermediateThrowEvent_0xxuh9e"
@@ "SequenceFlow_034nt5z" :> "SubProcess_1ggm3we"
@@ "SequenceFlow_1oxtfj2" :> "IntermediateThrowEvent_0xxuh9e"
@@ "SequenceFlow_1yblldx" :> "BoundaryEvent_1jast47"
@@ "SequenceFlow_0dyhbe0" :> "Task_05bgz5k"
@@ "SequenceFlow_1aj35wd" :> "StartEvent_1"
@@ "SequenceFlow_1hxg2dl" :> "Task_1ljmp3l"
@@ "SequenceFlow_0efj6hj" :> "ExclusiveGateway_121v81s"
@@ "SequenceFlow_06wfm19" :> "ExclusiveGateway_121v81s"
@@ "SequenceFlow_029fmhs" :> "StartEvent_134yuce"
@@ "SequenceFlow_19jmp5d" :> "ExclusiveGateway_0chq45h"
@@ "SequenceFlow_01hgmep" :> "StartEvent_1yq5hw0"
@@ "SequenceFlow_1fut9qx" :> "ExclusiveGateway_0nhvvs9"
@@ "SequenceFlow_19ixkyb" :> "IntermediateCatchEvent_0ufeqmr"
@@ "SequenceFlow_1k7hxgw" :> "ExclusiveGateway_0nhvvs9"
@@ "SequenceFlow_0s6c8vn" :> "IntermediateCatchEvent_14fmuo3"
@@ "SequenceFlow_13vx7cl" :> "ExclusiveGateway_0ngzdyp"

target ==
   "MessageFlow_1295wps" :> "IntermediateCatchEvent_0ufeqmr"
@@ "MessageFlow_13dqcc0" :> "IntermediateCatchEvent_14fmuo3"
@@ "SequenceFlow_034nt5z" :> "IntermediateThrowEvent_0xxuh9e"
@@ "SequenceFlow_1oxtfj2" :> "EndEvent_0v2esc4"
@@ "SequenceFlow_1yblldx" :> "Task_05bgz5k"
@@ "SequenceFlow_0dyhbe0" :> "EndEvent_00diytc"
@@ "SequenceFlow_1aj35wd" :> "SubProcess_1ggm3we"
@@ "SequenceFlow_1hxg2dl" :> "ExclusiveGateway_121v81s"
@@ "SequenceFlow_0efj6hj" :> "EndEvent_1ex5meo"
@@ "SequenceFlow_06wfm19" :> "ExclusiveGateway_0chq45h"
@@ "SequenceFlow_029fmhs" :> "ExclusiveGateway_0chq45h"
@@ "SequenceFlow_19jmp5d" :> "Task_1ljmp3l"
@@ "SequenceFlow_01hgmep" :> "ExclusiveGateway_0ngzdyp"
@@ "SequenceFlow_1fut9qx" :> "IntermediateCatchEvent_0ufeqmr"
@@ "SequenceFlow_19ixkyb" :> "ExclusiveGateway_0ngzdyp"
@@ "SequenceFlow_1k7hxgw" :> "IntermediateCatchEvent_14fmuo3"
@@ "SequenceFlow_0s6c8vn" :> "EndEvent_1c69md6"
@@ "SequenceFlow_13vx7cl" :> "ExclusiveGateway_0nhvvs9"

CatN ==
   "Process_1" :> Process
@@ "Process_0y7bmnu" :> Process
@@ "SubProcess_1ggm3we" :> SubProcess
@@ "IntermediateThrowEvent_0xxuh9e" :> ThrowMessageIntermediateEvent
@@ "EndEvent_00diytc" :> NoneEndEvent
@@ "Task_05bgz5k" :> SendTask
@@ "StartEvent_1" :> NoneStartEvent
@@ "BoundaryEvent_1jast47" :> TimerBoundaryEvent
@@ "EndEvent_0v2esc4" :> TerminateEndEvent
@@ "StartEvent_134yuce" :> NoneStartEvent
@@ "Task_1ljmp3l" :> AbstractTask
@@ "EndEvent_1ex5meo" :> NoneEndEvent
@@ "ExclusiveGateway_121v81s" :> ExclusiveOr
@@ "ExclusiveGateway_0chq45h" :> ExclusiveOr
@@ "StartEvent_1yq5hw0" :> NoneStartEvent
@@ "IntermediateCatchEvent_0ufeqmr" :> CatchMessageIntermediateEvent
@@ "IntermediateCatchEvent_14fmuo3" :> CatchMessageIntermediateEvent
@@ "EndEvent_1c69md6" :> TerminateEndEvent
@@ "ExclusiveGateway_0nhvvs9" :> EventBased
@@ "ExclusiveGateway_0ngzdyp" :> ExclusiveOr

CatE ==
   "MessageFlow_1295wps" :> MessageFlow
@@ "MessageFlow_13dqcc0" :> MessageFlow
@@ "SequenceFlow_034nt5z" :> NormalSeqFlow
@@ "SequenceFlow_1oxtfj2" :> NormalSeqFlow
@@ "SequenceFlow_1yblldx" :> NormalSeqFlow
@@ "SequenceFlow_0dyhbe0" :> NormalSeqFlow
@@ "SequenceFlow_1aj35wd" :> NormalSeqFlow
@@ "SequenceFlow_1hxg2dl" :> NormalSeqFlow
@@ "SequenceFlow_0efj6hj" :> NormalSeqFlow
@@ "SequenceFlow_06wfm19" :> NormalSeqFlow
@@ "SequenceFlow_029fmhs" :> NormalSeqFlow
@@ "SequenceFlow_19jmp5d" :> NormalSeqFlow
@@ "SequenceFlow_01hgmep" :> NormalSeqFlow
@@ "SequenceFlow_1fut9qx" :> NormalSeqFlow
@@ "SequenceFlow_19ixkyb" :> NormalSeqFlow
@@ "SequenceFlow_1k7hxgw" :> NormalSeqFlow
@@ "SequenceFlow_0s6c8vn" :> NormalSeqFlow
@@ "SequenceFlow_13vx7cl" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_1jast47" :> [ attachedTo |-> "SubProcess_1ggm3we", cancelActivity |-> FALSE ]

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

