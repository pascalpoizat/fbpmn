---------------- MODULE s001SimpleMove ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "PId" :> {  }

ContainRel ==
  "PId" :> { "StartEvent_1", "Event_0fkborc", "Activity_0z782bb" }

Node == { "PId", "StartEvent_1", "Event_0fkborc", "Activity_0z782bb" }

Edge == { "Flow_09a8um7", "Flow_0llicsy" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "Flow_09a8um7" :> "StartEvent_1"
@@ "Flow_0llicsy" :> "Activity_0z782bb"

target ==
   "Flow_09a8um7" :> "Activity_0z782bb"
@@ "Flow_0llicsy" :> "Event_0fkborc"

CatN ==
   "PId" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Event_0fkborc" :> NoneEndEvent
@@ "Activity_0z782bb" :> AbstractTask

CatE ==
   "Flow_09a8um7" :> NormalSeqFlow
@@ "Flow_0llicsy" :> NormalSeqFlow

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

