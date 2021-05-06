---------------- MODULE e053TSE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_1" :> {  }
  @@ "Process_1fvo71o" :> {  }

ContainRel ==
  "Process_1" :> { "NSE", "T1", "EE1" }
  @@ "Process_1fvo71o" :> { "StartEvent_04szy8h", "Task_0x899gn", "EndEvent_0gtkoek" }

Node == { "Process_1", "Process_1fvo71o", "NSE", "T1", "EE1", "StartEvent_04szy8h", "Task_0x899gn", "EndEvent_0gtkoek" }

Edge == { "SF1", "SF2", "SequenceFlow_0ru7vyn", "SequenceFlow_12856fs" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SF1" :> "NSE"
@@ "SF2" :> "T1"
@@ "SequenceFlow_0ru7vyn" :> "StartEvent_04szy8h"
@@ "SequenceFlow_12856fs" :> "Task_0x899gn"

target ==
   "SF1" :> "T1"
@@ "SF2" :> "EE1"
@@ "SequenceFlow_0ru7vyn" :> "Task_0x899gn"
@@ "SequenceFlow_12856fs" :> "EndEvent_0gtkoek"

CatN ==
   "Process_1" :> Process
@@ "Process_1fvo71o" :> Process
@@ "NSE" :> NoneStartEvent
@@ "T1" :> AbstractTask
@@ "EE1" :> NoneEndEvent
@@ "StartEvent_04szy8h" :> TimerStartEvent
@@ "Task_0x899gn" :> AbstractTask
@@ "EndEvent_0gtkoek" :> NoneEndEvent

CatE ==
   "SF1" :> NormalSeqFlow
@@ "SF2" :> NormalSeqFlow
@@ "SequenceFlow_0ru7vyn" :> NormalSeqFlow
@@ "SequenceFlow_12856fs" :> NormalSeqFlow

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

