---------------- MODULE s001SimpleMove ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

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

BaseLocation == { "f1", "f2", "f3", "f4", "f5", "f6", "r1", "r2", "b", "m" }

GroupLocation == { "toPlant", "planted", "toSpray", "sprayed" }

Location == GroupLocation \union BaseLocation

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


Var == { "here", "_", "locPId" }

varloc ==
   "PId" :> "locPId"

locvar ==
   "locPId" :> "PId"

Reachable ==
   "f1" :> { "b", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f2" :> { "b", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f3" :> { "b", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f4" :> { "f4", "f5", "f6", "m" }
@@ "f5" :> { "f4", "f5", "f6", "m" }
@@ "f6" :> { "f4", "f5", "f6", "m" }
@@ "r1" :> { "r1" }
@@ "r2" :> { "r2" }
@@ "b" :> { "b", "f4", "f5", "f6", "m" }
@@ "m" :> { "f4", "f5", "f6", "m" }

reachFrom(b) == UNION {Reachable[x] : x \in b}


cVar ==
  [ i \in {} |-> {}]

cKind ==
  [ i \in {} |-> {}]

cCond ==
  [ i \in {} |-> {}]


orderingSet == { }
order(a,b) == <<a,b>> \in orderingSet


aKind ==
   "Activity_0z782bb" :> ACT_MOVE

aUpdateVar ==
  [ i \in {} |-> {}]

aUpdateGMinus ==
  [ i \in {} |-> {}]

aUpdateGPlus ==
  [ i \in {} |-> {}]

aCond ==
   "Activity_0z782bb" :> "f_Activity_0z782bb"

def_f_Activity_0z782bb(v,s,p) == (reachFrom(v[varloc[p]]) \intersect s["toPlant"])



CodeCondition == { "f_Activity_0z782bb" }

evalF(v,s,p,f) ==
IF f = "f_Activity_0z782bb" THEN def_f_Activity_0z782bb(v,s,p)
ELSE {  }

startloc ==
   "PId" :> "f1"

startsub ==
   "toPlant" :> { "f1", "f2", "f3", "f4", "f5", "f6" }
@@ "planted" :> {  }
@@ "toSpray" :> {  }
@@ "sprayed" :> {  }



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

