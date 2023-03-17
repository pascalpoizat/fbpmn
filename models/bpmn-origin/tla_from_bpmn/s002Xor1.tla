---------------- MODULE s002Xor1 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net
Interest ==
  "PId" :> {  }
ContainRel ==
  "PId" :> { "StartEvent_1", "end_moved", "Gateway_0bb8o1z", "end_in_place", "Activity_0z782bb" }
Node == { "PId", "StartEvent_1", "end_moved", "Gateway_0bb8o1z", "end_in_place", "Activity_0z782bb" }
Edge == { "Flow_09a8um7", "Flow_0llicsy", "Flow_18ptpdh", "Flow_14b309w" }
Message == {  }
msgtype ==
  [ i \in {} |-> {}]

source ==
   "Flow_09a8um7" :> "StartEvent_1"@@ "Flow_0llicsy" :> "Activity_0z782bb"@@ "Flow_18ptpdh" :> "Gateway_0bb8o1z"@@ "Flow_14b309w" :> "Gateway_0bb8o1z"
target ==
   "Flow_09a8um7" :> "Gateway_0bb8o1z"@@ "Flow_0llicsy" :> "end_moved"@@ "Flow_18ptpdh" :> "Activity_0z782bb"@@ "Flow_14b309w" :> "end_in_place"
CatN ==
   "PId" :> Process@@ "StartEvent_1" :> NoneStartEvent@@ "end_moved" :> NoneEndEvent@@ "Gateway_0bb8o1z" :> ExclusiveOr@@ "end_in_place" :> NoneEndEvent@@ "Activity_0z782bb" :> AbstractTask
CatE ==
   "Flow_09a8um7" :> NormalSeqFlow@@ "Flow_0llicsy" :> NormalSeqFlow@@ "Flow_18ptpdh" :> ConditionalSeqFlow@@ "Flow_14b309w" :> DefaultSeqFlow
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
