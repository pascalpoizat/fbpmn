---------------- MODULE e033MBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> { "query", "cancellation" }
  @@ "Q_" :> { "confirmation", "estimate", "invoice", "results" }

ContainRel ==
  "P_" :> { "StartEvent_1", "Task_05seu1l", "Task_0yk02ke", "EndEvent_1yasgxk", "ExclusiveGateway_06st2fh", "IntermediateThrowEvent_16df5b4", "Task_1lnz72e", "Task_1ypg0u2", "BoundaryEvent_1fgc3dg" }
  @@ "Q_" :> { "StartEvent_1axpofs", "Task_0k7ip70", "IntermediateThrowEvent_0yo36nb", "ExclusiveGateway_0phbzc0", "IntermediateThrowEvent_1ewiw3i", "ExclusiveGateway_14e5fg8", "IntermediateThrowEvent_0nfi6to", "EndEvent_0l9fmhf", "ExclusiveGateway_06aycf0", "IntermediateThrowEvent_1s2ehzf", "IntermediateThrowEvent_1q2mw0e" }

Node == { "P_", "Q_", "StartEvent_1", "Task_05seu1l", "Task_0yk02ke", "EndEvent_1yasgxk", "ExclusiveGateway_06st2fh", "IntermediateThrowEvent_16df5b4", "Task_1lnz72e", "Task_1ypg0u2", "BoundaryEvent_1fgc3dg", "StartEvent_1axpofs", "Task_0k7ip70", "IntermediateThrowEvent_0yo36nb", "ExclusiveGateway_0phbzc0", "IntermediateThrowEvent_1ewiw3i", "ExclusiveGateway_14e5fg8", "IntermediateThrowEvent_0nfi6to", "EndEvent_0l9fmhf", "ExclusiveGateway_06aycf0", "IntermediateThrowEvent_1s2ehzf", "IntermediateThrowEvent_1q2mw0e" }

Edge == { "MessageFlow_0qo10kt", "MessageFlow_1a8bsa8", "MessageFlow_1r7fyxg", "MessageFlow_091cszi", "MessageFlow_1tq79cn", "MessageFlow_1okf1vd", "SequenceFlow_1wgoun9", "SequenceFlow_0698suh", "SequenceFlow_0k086s0", "SequenceFlow_1dte0vc", "SequenceFlow_0fplzau", "SequenceFlow_0o5vg8x", "SequenceFlow_1wtnl4z", "SequenceFlow_0nps006", "SequenceFlow_0v4m6o8", "SequenceFlow_0jq12xx", "SequenceFlow_0eej3d6", "SequenceFlow_096ubuj", "SequenceFlow_1oxapbj", "SequenceFlow_0f0ojke", "SequenceFlow_0k02j79", "SequenceFlow_0rjtib7", "SequenceFlow_1y1oo45", "SequenceFlow_1xvdo11", "SequenceFlow_0mgjt9y", "SequenceFlow_16ovyt7" }

Message == { "query", "estimate", "cancellation", "confirmation", "results", "invoice" }

msgtype ==
   "MessageFlow_0qo10kt" :> "query"
@@ "MessageFlow_1a8bsa8" :> "estimate"
@@ "MessageFlow_1r7fyxg" :> "cancellation"
@@ "MessageFlow_091cszi" :> "confirmation"
@@ "MessageFlow_1tq79cn" :> "results"
@@ "MessageFlow_1okf1vd" :> "invoice"


source ==
   "MessageFlow_0qo10kt" :> "Task_0k7ip70"
@@ "MessageFlow_1a8bsa8" :> "Task_05seu1l"
@@ "MessageFlow_1r7fyxg" :> "IntermediateThrowEvent_1ewiw3i"
@@ "MessageFlow_091cszi" :> "IntermediateThrowEvent_16df5b4"
@@ "MessageFlow_1tq79cn" :> "Task_1ypg0u2"
@@ "MessageFlow_1okf1vd" :> "Task_1lnz72e"
@@ "SequenceFlow_1wgoun9" :> "IntermediateThrowEvent_16df5b4"
@@ "SequenceFlow_0698suh" :> "ExclusiveGateway_06st2fh"
@@ "SequenceFlow_0k086s0" :> "Task_1lnz72e"
@@ "SequenceFlow_1dte0vc" :> "BoundaryEvent_1fgc3dg"
@@ "SequenceFlow_0fplzau" :> "Task_1ypg0u2"
@@ "SequenceFlow_0o5vg8x" :> "Task_0yk02ke"
@@ "SequenceFlow_1wtnl4z" :> "Task_05seu1l"
@@ "SequenceFlow_0nps006" :> "StartEvent_1"
@@ "SequenceFlow_0v4m6o8" :> "IntermediateThrowEvent_1q2mw0e"
@@ "SequenceFlow_0jq12xx" :> "IntermediateThrowEvent_1s2ehzf"
@@ "SequenceFlow_0eej3d6" :> "ExclusiveGateway_06aycf0"
@@ "SequenceFlow_096ubuj" :> "IntermediateThrowEvent_0nfi6to"
@@ "SequenceFlow_1oxapbj" :> "ExclusiveGateway_14e5fg8"
@@ "SequenceFlow_0f0ojke" :> "ExclusiveGateway_14e5fg8"
@@ "SequenceFlow_0k02j79" :> "ExclusiveGateway_0phbzc0"
@@ "SequenceFlow_0rjtib7" :> "IntermediateThrowEvent_1ewiw3i"
@@ "SequenceFlow_1y1oo45" :> "ExclusiveGateway_0phbzc0"
@@ "SequenceFlow_1xvdo11" :> "IntermediateThrowEvent_0yo36nb"
@@ "SequenceFlow_0mgjt9y" :> "Task_0k7ip70"
@@ "SequenceFlow_16ovyt7" :> "StartEvent_1axpofs"

target ==
   "MessageFlow_0qo10kt" :> "StartEvent_1"
@@ "MessageFlow_1a8bsa8" :> "IntermediateThrowEvent_0yo36nb"
@@ "MessageFlow_1r7fyxg" :> "BoundaryEvent_1fgc3dg"
@@ "MessageFlow_091cszi" :> "IntermediateThrowEvent_1s2ehzf"
@@ "MessageFlow_1tq79cn" :> "IntermediateThrowEvent_0nfi6to"
@@ "MessageFlow_1okf1vd" :> "IntermediateThrowEvent_1q2mw0e"
@@ "SequenceFlow_1wgoun9" :> "ExclusiveGateway_06st2fh"
@@ "SequenceFlow_0698suh" :> "EndEvent_1yasgxk"
@@ "SequenceFlow_0k086s0" :> "ExclusiveGateway_06st2fh"
@@ "SequenceFlow_1dte0vc" :> "IntermediateThrowEvent_16df5b4"
@@ "SequenceFlow_0fplzau" :> "Task_1lnz72e"
@@ "SequenceFlow_0o5vg8x" :> "Task_1ypg0u2"
@@ "SequenceFlow_1wtnl4z" :> "Task_0yk02ke"
@@ "SequenceFlow_0nps006" :> "Task_05seu1l"
@@ "SequenceFlow_0v4m6o8" :> "ExclusiveGateway_06aycf0"
@@ "SequenceFlow_0jq12xx" :> "ExclusiveGateway_06aycf0"
@@ "SequenceFlow_0eej3d6" :> "EndEvent_0l9fmhf"
@@ "SequenceFlow_096ubuj" :> "IntermediateThrowEvent_1q2mw0e"
@@ "SequenceFlow_1oxapbj" :> "IntermediateThrowEvent_0nfi6to"
@@ "SequenceFlow_0f0ojke" :> "IntermediateThrowEvent_1s2ehzf"
@@ "SequenceFlow_0k02j79" :> "ExclusiveGateway_14e5fg8"
@@ "SequenceFlow_0rjtib7" :> "ExclusiveGateway_14e5fg8"
@@ "SequenceFlow_1y1oo45" :> "IntermediateThrowEvent_1ewiw3i"
@@ "SequenceFlow_1xvdo11" :> "ExclusiveGateway_0phbzc0"
@@ "SequenceFlow_0mgjt9y" :> "IntermediateThrowEvent_0yo36nb"
@@ "SequenceFlow_16ovyt7" :> "Task_0k7ip70"

CatN ==
   "P_" :> Process
@@ "Q_" :> Process
@@ "StartEvent_1" :> MessageStartEvent
@@ "Task_05seu1l" :> SendTask
@@ "Task_0yk02ke" :> AbstractTask
@@ "EndEvent_1yasgxk" :> NoneEndEvent
@@ "ExclusiveGateway_06st2fh" :> ExclusiveOr
@@ "IntermediateThrowEvent_16df5b4" :> ThrowMessageIntermediateEvent
@@ "Task_1lnz72e" :> SendTask
@@ "Task_1ypg0u2" :> SendTask
@@ "BoundaryEvent_1fgc3dg" :> MessageBoundaryEvent
@@ "StartEvent_1axpofs" :> NoneStartEvent
@@ "Task_0k7ip70" :> SendTask
@@ "IntermediateThrowEvent_0yo36nb" :> CatchMessageIntermediateEvent
@@ "ExclusiveGateway_0phbzc0" :> ExclusiveOr
@@ "IntermediateThrowEvent_1ewiw3i" :> ThrowMessageIntermediateEvent
@@ "ExclusiveGateway_14e5fg8" :> EventBased
@@ "IntermediateThrowEvent_0nfi6to" :> CatchMessageIntermediateEvent
@@ "EndEvent_0l9fmhf" :> NoneEndEvent
@@ "ExclusiveGateway_06aycf0" :> ExclusiveOr
@@ "IntermediateThrowEvent_1s2ehzf" :> CatchMessageIntermediateEvent
@@ "IntermediateThrowEvent_1q2mw0e" :> CatchMessageIntermediateEvent

CatE ==
   "MessageFlow_0qo10kt" :> MessageFlow
@@ "MessageFlow_1a8bsa8" :> MessageFlow
@@ "MessageFlow_1r7fyxg" :> MessageFlow
@@ "MessageFlow_091cszi" :> MessageFlow
@@ "MessageFlow_1tq79cn" :> MessageFlow
@@ "MessageFlow_1okf1vd" :> MessageFlow
@@ "SequenceFlow_1wgoun9" :> NormalSeqFlow
@@ "SequenceFlow_0698suh" :> NormalSeqFlow
@@ "SequenceFlow_0k086s0" :> NormalSeqFlow
@@ "SequenceFlow_1dte0vc" :> NormalSeqFlow
@@ "SequenceFlow_0fplzau" :> NormalSeqFlow
@@ "SequenceFlow_0o5vg8x" :> NormalSeqFlow
@@ "SequenceFlow_1wtnl4z" :> NormalSeqFlow
@@ "SequenceFlow_0nps006" :> NormalSeqFlow
@@ "SequenceFlow_0v4m6o8" :> NormalSeqFlow
@@ "SequenceFlow_0jq12xx" :> NormalSeqFlow
@@ "SequenceFlow_0eej3d6" :> NormalSeqFlow
@@ "SequenceFlow_096ubuj" :> NormalSeqFlow
@@ "SequenceFlow_1oxapbj" :> NormalSeqFlow
@@ "SequenceFlow_0f0ojke" :> NormalSeqFlow
@@ "SequenceFlow_0k02j79" :> DefaultSeqFlow
@@ "SequenceFlow_0rjtib7" :> NormalSeqFlow
@@ "SequenceFlow_1y1oo45" :> ConditionalSeqFlow
@@ "SequenceFlow_1xvdo11" :> NormalSeqFlow
@@ "SequenceFlow_0mgjt9y" :> NormalSeqFlow
@@ "SequenceFlow_16ovyt7" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_1fgc3dg" :> [ attachedTo |-> "Task_0yk02ke", cancelActivity |-> TRUE ]

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

