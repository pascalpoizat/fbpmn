---------------- MODULE s004Xor3 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "PId" :> {  }

ContainRel ==
  "PId" :> { "StartEvent_1", "Gateway_0bb8o1z", "Activity_0z782bb", "Activity_11g6ot8", "Event_01pf838" }

Node == { "PId", "StartEvent_1", "Gateway_0bb8o1z", "Activity_0z782bb", "Activity_11g6ot8", "Event_01pf838" }

Edge == { "Flow_09a8um7", "Flow_18ptpdh", "Flow_0ipe2sk", "Flow_0evvsn6", "Flow_11sy0ae" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "Flow_09a8um7" :> "StartEvent_1"
@@ "Flow_18ptpdh" :> "Gateway_0bb8o1z"
@@ "Flow_0ipe2sk" :> "Activity_0z782bb"
@@ "Flow_0evvsn6" :> "Activity_11g6ot8"
@@ "Flow_11sy0ae" :> "Gateway_0bb8o1z"

target ==
   "Flow_09a8um7" :> "Gateway_0bb8o1z"
@@ "Flow_18ptpdh" :> "Activity_0z782bb"
@@ "Flow_0ipe2sk" :> "Activity_11g6ot8"
@@ "Flow_0evvsn6" :> "Gateway_0bb8o1z"
@@ "Flow_11sy0ae" :> "Event_01pf838"

CatN ==
   "PId" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Gateway_0bb8o1z" :> ExclusiveOr
@@ "Activity_0z782bb" :> AbstractTask
@@ "Activity_11g6ot8" :> AbstractTask
@@ "Event_01pf838" :> NoneEndEvent

CatE ==
   "Flow_09a8um7" :> NormalSeqFlow
@@ "Flow_18ptpdh" :> ConditionalSeqFlow
@@ "Flow_0ipe2sk" :> NormalSeqFlow
@@ "Flow_0evvsn6" :> NormalSeqFlow
@@ "Flow_11sy0ae" :> DefaultSeqFlow

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

