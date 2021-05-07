---------------- MODULE s009ConditionOrdering ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

Interest ==
  "PId" :> {  }

ContainRel ==
  "PId" :> { "endF2", "endInPlace", "endF3", "xor", "StartEvent_1", "Activity_071wli2", "Activity_18vh6pp" }

Node == { "PId", "endF2", "endInPlace", "endF3", "xor", "StartEvent_1", "Activity_071wli2", "Activity_18vh6pp" }

Edge == { "Flow_09a8um7", "flow_to_f2", "default_flow", "flow_to_f3", "Flow_1bc6u3c", "Flow_1ddop94" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "Flow_09a8um7" :> "StartEvent_1"
@@ "flow_to_f2" :> "xor"
@@ "default_flow" :> "xor"
@@ "flow_to_f3" :> "xor"
@@ "Flow_1bc6u3c" :> "Activity_071wli2"
@@ "Flow_1ddop94" :> "Activity_18vh6pp"

target ==
   "Flow_09a8um7" :> "xor"
@@ "flow_to_f2" :> "Activity_071wli2"
@@ "default_flow" :> "endInPlace"
@@ "flow_to_f3" :> "Activity_18vh6pp"
@@ "Flow_1bc6u3c" :> "endF2"
@@ "Flow_1ddop94" :> "endF3"

CatN ==
   "PId" :> Process
@@ "endF2" :> NoneEndEvent
@@ "endInPlace" :> NoneEndEvent
@@ "endF3" :> NoneEndEvent
@@ "xor" :> ExclusiveOr
@@ "StartEvent_1" :> NoneStartEvent
@@ "Activity_071wli2" :> AbstractTask
@@ "Activity_18vh6pp" :> AbstractTask

CatE ==
   "Flow_09a8um7" :> NormalSeqFlow
@@ "flow_to_f2" :> ConditionalSeqFlow
@@ "default_flow" :> DefaultSeqFlow
@@ "flow_to_f3" :> ConditionalSeqFlow
@@ "Flow_1bc6u3c" :> NormalSeqFlow
@@ "Flow_1ddop94" :> NormalSeqFlow

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
   "flow_to_f2" :> "_"
@@ "flow_to_f3" :> "_"

cKind ==
   "flow_to_f2" :> Some
@@ "flow_to_f3" :> Some

cCond ==
   "flow_to_f2" :> "f_flow_to_f2"
@@ "flow_to_f3" :> "f_flow_to_f3"

def_f_flow_to_f2(v,s,p) == (({ "f2" } \intersect s["toPlant"]) \intersect reachFrom(v[varloc[p]]))

def_f_flow_to_f3(v,s,p) == (({ "f3" } \intersect s["toPlant"]) \intersect reachFrom(v[varloc[p]]))


orderingSet == { }
order(a,b) == <<a,b>> \in orderingSet


aKind ==
   "Activity_071wli2" :> ACT_MOVE
@@ "Activity_18vh6pp" :> ACT_MOVE

aUpdateVar ==
  [ i \in {} |-> {}]

aUpdateGMinus ==
  [ i \in {} |-> {}]

aUpdateGPlus ==
  [ i \in {} |-> {}]

aCond ==
   "Activity_071wli2" :> "f_Activity_071wli2"
@@ "Activity_18vh6pp" :> "f_Activity_18vh6pp"

def_f_Activity_071wli2(v,s,p) == { "f2" }

def_f_Activity_18vh6pp(v,s,p) == { "f3" }



CodeCondition == { "f_Activity_071wli2", "f_Activity_18vh6pp", "f_flow_to_f2", "f_flow_to_f3" }

evalF(v,s,p,f) ==
IF f = "f_Activity_071wli2" THEN def_f_Activity_071wli2(v,s,p)
ELSE IF f = "f_Activity_18vh6pp" THEN def_f_Activity_18vh6pp(v,s,p)
ELSE IF f = "f_flow_to_f2" THEN def_f_flow_to_f2(v,s,p)
ELSE IF f = "f_flow_to_f3" THEN def_f_flow_to_f3(v,s,p)
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

