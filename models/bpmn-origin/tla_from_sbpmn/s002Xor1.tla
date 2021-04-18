---------------- MODULE s002Xor1 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

Interest ==
  "PId" :> {  }

ContainRel ==
  "PId" :> { "StartEvent_1", "Event_0fkborc", "Gateway_0bb8o1z", "Event_1hpd68d", "Activity_0z782bb" }

Node == { "PId", "StartEvent_1", "Event_0fkborc", "Gateway_0bb8o1z", "Event_1hpd68d", "Activity_0z782bb" }

Edge == { "Flow_09a8um7", "Flow_0llicsy", "Flow_18ptpdh", "Flow_14b309w" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "Flow_09a8um7" :> "StartEvent_1"
@@ "Flow_0llicsy" :> "Activity_0z782bb"
@@ "Flow_18ptpdh" :> "Gateway_0bb8o1z"
@@ "Flow_14b309w" :> "Gateway_0bb8o1z"

target ==
   "Flow_09a8um7" :> "Gateway_0bb8o1z"
@@ "Flow_0llicsy" :> "Event_0fkborc"
@@ "Flow_18ptpdh" :> "Activity_0z782bb"
@@ "Flow_14b309w" :> "Event_1hpd68d"

CatN ==
   "PId" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Event_0fkborc" :> NoneEndEvent
@@ "Gateway_0bb8o1z" :> ExclusiveOr
@@ "Event_1hpd68d" :> NoneEndEvent
@@ "Activity_0z782bb" :> AbstractTask

CatE ==
   "Flow_09a8um7" :> NormalSeqFlow
@@ "Flow_0llicsy" :> NormalSeqFlow
@@ "Flow_18ptpdh" :> ConditionalSeqFlow
@@ "Flow_14b309w" :> DefaultSeqFlow

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


Var == { "here", "_", "z", "locPId" }

varloc ==
   "PId" :> "locPId"

locvar ==
   "locPId" :> "PId"

outgoingSpace(n) == { e \in SpaceEdge : SpaceSource[e] = n } 

succSpa(n) == { SpaceTarget[e] : e \in outgoingSpace(n) } 

RECURSIVE succsNew(_, _, _)
succsNew (n, A, B) == IF UNION{B} \ UNION{A} = {} THEN B
                              ELSE LET s == CHOOSE s \in UNION{UNION{B} \ UNION{A}} : TRUE
                                  IN succsNew(n, UNION{A \union {s}}, UNION{B \union UNION{succSpa(s)}}) 

succsSpace == [b \in BaseLocation |-> succsNew (b, {b}, succSpa(b))]

RECURSIVE nextLocs(_, _, _)
nextLocs (n, A, B) == IF UNION{B} \ UNION{A} = {} THEN B
                              ELSE LET s == CHOOSE s \in UNION{UNION{B} \ UNION{A}} : TRUE
                                  IN nextLocs(n, UNION{A \union {s}}, UNION{B \union UNION{succsSpace[s]}}) 

reach(v,p) == nextLocs (v[varloc[p]], {v[varloc[p]]} , succsSpace[v[varloc[p]]])

cVar ==
   "Flow_18ptpdh" :> "z"

cKind ==
   "Flow_18ptpdh" :> All

cCond ==
   "Flow_18ptpdh" :> "f_Flow_18ptpdh"

def_f_Flow_18ptpdh(v,s,p) == (reach(v,p) \intersect s["toPlant"])





evalF(v,s,p,f) ==
IF f = "f_Activity_0z782bb" THEN def_f_Activity_0z782bb(v,s,p)
ELSE IF f = "f_Flow_18ptpdh" THEN def_f_Flow_18ptpdh(v,s,p)
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

INSTANCE PWSSemantics

================================================================

