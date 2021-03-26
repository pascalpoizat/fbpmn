---------------- MODULE s004Xor3 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

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

BaseLocation == { "f1", "f2", "f3", "f4", "f5", "f6", "r1", "r2", "b", "m" }

GroupLocation == { "toPlant", "planted", "toSpray", "sprayed" }

Locations == GroupLocation \union BaseLocation

SpaceEdge == { "se_0", "se_1", "se_2", "se_3", "se_4", "se_5", "se_6", "se_7", "se_8", "se_9", "se_10", "se_11", "se_12" }

SpaceSource ==
   "se_0" :> "f1"
@@ "se_1" :> "f2"
@@ "se_2" :> "f2"
@@ "se_3" :> "f3"
@@ "se_4" :> "f2"
@@ "se_5" :> "b"
@@ "se_6" :> "f4"
@@ "se_7" :> "f5"
@@ "se_8" :> "f5"
@@ "se_9" :> "f6"
@@ "se_10" :> "f6"
@@ "se_11" :> "m"
@@ "se_12" :> "m"

SpaceTarget ==
   "se_0" :> "f2"
@@ "se_1" :> "f1"
@@ "se_2" :> "f3"
@@ "se_3" :> "f2"
@@ "se_4" :> "b"
@@ "se_5" :> "f5"
@@ "se_6" :> "f5"
@@ "se_7" :> "f4"
@@ "se_8" :> "f6"
@@ "se_9" :> "f5"
@@ "se_10" :> "m"
@@ "se_11" :> "f6"
@@ "se_12" :> "f5"


Var == {  }

varloc ==
   "PId" :> "locPId"

locvar ==
   "locPId" :> "PId"







WF == INSTANCE PWSWellFormed
ASSUME WF!WellTyped
ASSUME WF!WellFormedness

ConstraintNode == TRUE \* none
ConstraintEdge == TRUE \* none
Constraint == TRUE     \* none
INSTANCE PWSConstraints

INSTANCE PWSSemantics

================================================================

