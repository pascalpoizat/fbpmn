---------------- MODULE eXXX_TBENICycleDurationInf ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Pid" :> {  }

ContainRel ==
  "Pid" :> { "sp", "se", "ee2", "t2", "ee1", "t3", "be" }
  @@ "sp" :> { "t1", "StartEvent_0y9n6er", "eeSP" }

Node == { "Pid", "sp", "se", "ee2", "t2", "ee1", "t3", "be", "t1", "StartEvent_0y9n6er", "eeSP" }

Edge == { "SequenceFlow_1351e66", "SequenceFlow_069yln3", "SequenceFlow_0210zve", "SequenceFlow_0lpe900", "SequenceFlow_1ckj6jx", "SequenceFlow_18ve5j0", "SequenceFlow_0xvib5s" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_1351e66" :> "se"
@@ "SequenceFlow_069yln3" :> "sp"
@@ "SequenceFlow_0210zve" :> "t2"
@@ "SequenceFlow_0lpe900" :> "t3"
@@ "SequenceFlow_1ckj6jx" :> "be"
@@ "SequenceFlow_18ve5j0" :> "StartEvent_0y9n6er"
@@ "SequenceFlow_0xvib5s" :> "t1"

target ==
   "SequenceFlow_1351e66" :> "sp"
@@ "SequenceFlow_069yln3" :> "t2"
@@ "SequenceFlow_0210zve" :> "ee2"
@@ "SequenceFlow_0lpe900" :> "ee1"
@@ "SequenceFlow_1ckj6jx" :> "t3"
@@ "SequenceFlow_18ve5j0" :> "t1"
@@ "SequenceFlow_0xvib5s" :> "eeSP"

CatN ==
   "Pid" :> Process
@@ "sp" :> SubProcess
@@ "se" :> NoneStartEvent
@@ "ee2" :> NoneEndEvent
@@ "t2" :> AbstractTask
@@ "ee1" :> NoneEndEvent
@@ "t3" :> AbstractTask
@@ "be" :> TimerBoundaryEvent
@@ "t1" :> AbstractTask
@@ "StartEvent_0y9n6er" :> NoneStartEvent
@@ "eeSP" :> NoneEndEvent

CatE ==
   "SequenceFlow_1351e66" :> NormalSeqFlow
@@ "SequenceFlow_069yln3" :> NormalSeqFlow
@@ "SequenceFlow_0210zve" :> NormalSeqFlow
@@ "SequenceFlow_0lpe900" :> NormalSeqFlow
@@ "SequenceFlow_1ckj6jx" :> NormalSeqFlow
@@ "SequenceFlow_18ve5j0" :> NormalSeqFlow
@@ "SequenceFlow_0xvib5s" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "be" :> [ attachedTo |-> "sp", cancelActivity |-> FALSE ]

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

