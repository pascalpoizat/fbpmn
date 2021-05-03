---------------- MODULE s006Robots2 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

Interest ==
  "ControllerId" :> { "ACK", "ERR" }
  @@ "PlanterId" :> { "DIRECT", "ACTIVATE", "DEACTIVATE" }

ContainRel ==
  "Activity_1jcadcm" :> { "Event_0syt2y2", "Activity_0jootbn", "Gateway_0nml6ij", "Event_03je60h", "Event_0kegwa2", "Gateway_0hg0uq5", "Gateway_1xyjdit", "Activity_1xs44yy", "Activity_01kew4w" }
  @@ "ControllerId" :> { "Gateway_0qgs992", "Activity_0id691h", "Gateway_0wl6a1o", "Event_0bxauwm", "StartEvent_1", "Gateway_0ok6126", "Event_0gwjxex", "Activity_0qbls7q", "Event_1et46oa", "Event_1pwlc9i", "Event_1i5je9n" }
  @@ "PlanterId" :> { "Event_1matb53", "Activity_0c5l85e", "Activity_1jcadcm", "Event_1k7stxl", "Gateway_0nq1hkt", "Activity_04y084u", "Event_0ci0tt9", "Activity_00galsb", "Activity_0c215j4", "Event_13r5sdw" }

Node == { "ControllerId", "PlanterId", "Gateway_0qgs992", "Activity_0id691h", "Gateway_0wl6a1o", "Event_0bxauwm", "StartEvent_1", "Gateway_0ok6126", "Event_0gwjxex", "Activity_0qbls7q", "Event_1et46oa", "Event_1pwlc9i", "Event_1i5je9n", "Event_1matb53", "Activity_0c5l85e", "Activity_1jcadcm", "Event_1k7stxl", "Gateway_0nq1hkt", "Activity_04y084u", "Event_0ci0tt9", "Activity_00galsb", "Activity_0c215j4", "Event_13r5sdw", "Event_0syt2y2", "Activity_0jootbn", "Gateway_0nml6ij", "Event_03je60h", "Event_0kegwa2", "Gateway_0hg0uq5", "Gateway_1xyjdit", "Activity_1xs44yy", "Activity_01kew4w" }

Edge == { "Flow_1c80fvc", "Flow_1q3i58t", "Flow_05gqmpv", "Flow_0ehcsg3", "Flow_03khyvp", "Flow_1maux1g", "Flow_04ffiyw", "Flow_10neqt1", "Flow_0ep8hv4", "Flow_0qdi3sr", "Flow_07deyd6", "Flow_1mj2hsk", "Flow_0m9uce7", "Flow_1wf4er6", "Flow_0gh7btl", "Flow_00b7crz", "Flow_0lbxlpn", "Flow_0i8hiam", "Flow_14hbae4", "Flow_1n1ra56", "Flow_0qbvxf7", "Flow_1skh2ra", "Flow_1wczndj", "Flow_0drx7uh", "Flow_0ik7oa8", "Flow_1alj9in", "Flow_0q7wp3m", "Flow_0l3fimu", "Flow_1rsrumf", "Flow_0owe6ra", "Flow_1p7v2y8", "Flow_12jkr8q", "Flow_17fyu56", "Flow_1alyuap", "Flow_0099ioz" }

Message == { "ACTIVATE", "DEACTIVATE", "DIRECT", "ERR", "ACK" }

msgtype ==
   "Flow_1c80fvc" :> "ACTIVATE"
@@ "Flow_1q3i58t" :> "DEACTIVATE"
@@ "Flow_05gqmpv" :> "DIRECT"
@@ "Flow_0ehcsg3" :> "ERR"
@@ "Flow_03khyvp" :> "ACK"


source ==
   "Flow_1c80fvc" :> "Event_0bxauwm"
@@ "Flow_1q3i58t" :> "Event_0gwjxex"
@@ "Flow_05gqmpv" :> "Activity_0id691h"
@@ "Flow_0ehcsg3" :> "Event_03je60h"
@@ "Flow_03khyvp" :> "Event_0kegwa2"
@@ "Flow_1maux1g" :> "StartEvent_1"
@@ "Flow_04ffiyw" :> "Gateway_0qgs992"
@@ "Flow_10neqt1" :> "Gateway_0qgs992"
@@ "Flow_0ep8hv4" :> "Event_0bxauwm"
@@ "Flow_0qdi3sr" :> "Activity_0id691h"
@@ "Flow_07deyd6" :> "Gateway_0wl6a1o"
@@ "Flow_1mj2hsk" :> "Gateway_0wl6a1o"
@@ "Flow_0m9uce7" :> "Event_1et46oa"
@@ "Flow_1wf4er6" :> "Activity_0qbls7q"
@@ "Flow_0gh7btl" :> "Event_1pwlc9i"
@@ "Flow_00b7crz" :> "Gateway_0ok6126"
@@ "Flow_0lbxlpn" :> "Event_0gwjxex"
@@ "Flow_0i8hiam" :> "Event_1matb53"
@@ "Flow_14hbae4" :> "Activity_0c5l85e"
@@ "Flow_1n1ra56" :> "Event_13r5sdw"
@@ "Flow_0qbvxf7" :> "Activity_0c215j4"
@@ "Flow_1skh2ra" :> "Gateway_0nq1hkt"
@@ "Flow_1wczndj" :> "Gateway_0nq1hkt"
@@ "Flow_0drx7uh" :> "Activity_00galsb"
@@ "Flow_0ik7oa8" :> "Activity_04y084u"
@@ "Flow_1alj9in" :> "Activity_0jootbn"
@@ "Flow_0q7wp3m" :> "Gateway_0nml6ij"
@@ "Flow_0l3fimu" :> "Gateway_0nml6ij"
@@ "Flow_1rsrumf" :> "Event_03je60h"
@@ "Flow_0owe6ra" :> "Event_0syt2y2"
@@ "Flow_1p7v2y8" :> "Gateway_1xyjdit"
@@ "Flow_12jkr8q" :> "Gateway_0hg0uq5"
@@ "Flow_17fyu56" :> "Activity_1xs44yy"
@@ "Flow_1alyuap" :> "Activity_01kew4w"
@@ "Flow_0099ioz" :> "Event_0kegwa2"

target ==
   "Flow_1c80fvc" :> "Event_1matb53"
@@ "Flow_1q3i58t" :> "Event_13r5sdw"
@@ "Flow_05gqmpv" :> "Activity_0jootbn"
@@ "Flow_0ehcsg3" :> "Event_1pwlc9i"
@@ "Flow_03khyvp" :> "Event_1et46oa"
@@ "Flow_1maux1g" :> "Event_0bxauwm"
@@ "Flow_04ffiyw" :> "Gateway_0ok6126"
@@ "Flow_10neqt1" :> "Activity_0id691h"
@@ "Flow_0ep8hv4" :> "Gateway_0qgs992"
@@ "Flow_0qdi3sr" :> "Gateway_0wl6a1o"
@@ "Flow_07deyd6" :> "Event_1et46oa"
@@ "Flow_1mj2hsk" :> "Event_1pwlc9i"
@@ "Flow_0m9uce7" :> "Activity_0qbls7q"
@@ "Flow_1wf4er6" :> "Gateway_0qgs992"
@@ "Flow_0gh7btl" :> "Gateway_0ok6126"
@@ "Flow_00b7crz" :> "Event_0gwjxex"
@@ "Flow_0lbxlpn" :> "Event_1i5je9n"
@@ "Flow_0i8hiam" :> "Activity_0c5l85e"
@@ "Flow_14hbae4" :> "Activity_1jcadcm"
@@ "Flow_1n1ra56" :> "Gateway_0nq1hkt"
@@ "Flow_0qbvxf7" :> "Event_1k7stxl"
@@ "Flow_1skh2ra" :> "Activity_00galsb"
@@ "Flow_1wczndj" :> "Activity_04y084u"
@@ "Flow_0drx7uh" :> "Activity_0c215j4"
@@ "Flow_0ik7oa8" :> "Event_0ci0tt9"
@@ "Flow_1alj9in" :> "Gateway_0nml6ij"
@@ "Flow_0q7wp3m" :> "Activity_1xs44yy"
@@ "Flow_0l3fimu" :> "Event_03je60h"
@@ "Flow_1rsrumf" :> "Gateway_0hg0uq5"
@@ "Flow_0owe6ra" :> "Gateway_1xyjdit"
@@ "Flow_1p7v2y8" :> "Activity_0jootbn"
@@ "Flow_12jkr8q" :> "Gateway_1xyjdit"
@@ "Flow_17fyu56" :> "Activity_01kew4w"
@@ "Flow_1alyuap" :> "Event_0kegwa2"
@@ "Flow_0099ioz" :> "Gateway_0hg0uq5"

CatN ==
   "ControllerId" :> Process
@@ "PlanterId" :> Process
@@ "Gateway_0qgs992" :> ExclusiveOr
@@ "Activity_0id691h" :> SendTask
@@ "Gateway_0wl6a1o" :> EventBased
@@ "Event_0bxauwm" :> ThrowMessageIntermediateEvent
@@ "StartEvent_1" :> NoneStartEvent
@@ "Gateway_0ok6126" :> ExclusiveOr
@@ "Event_0gwjxex" :> ThrowMessageIntermediateEvent
@@ "Activity_0qbls7q" :> AbstractTask
@@ "Event_1et46oa" :> CatchMessageIntermediateEvent
@@ "Event_1pwlc9i" :> CatchMessageIntermediateEvent
@@ "Event_1i5je9n" :> NoneEndEvent
@@ "Event_1matb53" :> MessageStartEvent
@@ "Activity_0c5l85e" :> AbstractTask
@@ "Activity_1jcadcm" :> SubProcess
@@ "Event_1k7stxl" :> NoneEndEvent
@@ "Gateway_0nq1hkt" :> ExclusiveOr
@@ "Activity_04y084u" :> AbstractTask
@@ "Event_0ci0tt9" :> NoneEndEvent
@@ "Activity_00galsb" :> AbstractTask
@@ "Activity_0c215j4" :> AbstractTask
@@ "Event_13r5sdw" :> MessageBoundaryEvent
@@ "Event_0syt2y2" :> NoneStartEvent
@@ "Activity_0jootbn" :> ReceiveTask
@@ "Gateway_0nml6ij" :> ExclusiveOr
@@ "Event_03je60h" :> ThrowMessageIntermediateEvent
@@ "Event_0kegwa2" :> ThrowMessageIntermediateEvent
@@ "Gateway_0hg0uq5" :> ExclusiveOr
@@ "Gateway_1xyjdit" :> ExclusiveOr
@@ "Activity_1xs44yy" :> AbstractTask
@@ "Activity_01kew4w" :> AbstractTask

CatE ==
   "Flow_1c80fvc" :> MessageFlow
@@ "Flow_1q3i58t" :> MessageFlow
@@ "Flow_05gqmpv" :> MessageFlow
@@ "Flow_0ehcsg3" :> MessageFlow
@@ "Flow_03khyvp" :> MessageFlow
@@ "Flow_1maux1g" :> NormalSeqFlow
@@ "Flow_04ffiyw" :> DefaultSeqFlow
@@ "Flow_10neqt1" :> ConditionalSeqFlow
@@ "Flow_0ep8hv4" :> NormalSeqFlow
@@ "Flow_0qdi3sr" :> NormalSeqFlow
@@ "Flow_07deyd6" :> NormalSeqFlow
@@ "Flow_1mj2hsk" :> NormalSeqFlow
@@ "Flow_0m9uce7" :> NormalSeqFlow
@@ "Flow_1wf4er6" :> NormalSeqFlow
@@ "Flow_0gh7btl" :> NormalSeqFlow
@@ "Flow_00b7crz" :> NormalSeqFlow
@@ "Flow_0lbxlpn" :> NormalSeqFlow
@@ "Flow_0i8hiam" :> NormalSeqFlow
@@ "Flow_14hbae4" :> NormalSeqFlow
@@ "Flow_1n1ra56" :> NormalSeqFlow
@@ "Flow_0qbvxf7" :> NormalSeqFlow
@@ "Flow_1skh2ra" :> ConditionalSeqFlow
@@ "Flow_1wczndj" :> DefaultSeqFlow
@@ "Flow_0drx7uh" :> NormalSeqFlow
@@ "Flow_0ik7oa8" :> NormalSeqFlow
@@ "Flow_1alj9in" :> NormalSeqFlow
@@ "Flow_0q7wp3m" :> ConditionalSeqFlow
@@ "Flow_0l3fimu" :> DefaultSeqFlow
@@ "Flow_1rsrumf" :> NormalSeqFlow
@@ "Flow_0owe6ra" :> NormalSeqFlow
@@ "Flow_1p7v2y8" :> NormalSeqFlow
@@ "Flow_12jkr8q" :> NormalSeqFlow
@@ "Flow_17fyu56" :> NormalSeqFlow
@@ "Flow_1alyuap" :> NormalSeqFlow
@@ "Flow_0099ioz" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "Event_13r5sdw" :> [ attachedTo |-> "Activity_1jcadcm", cancelActivity |-> TRUE ]

BaseLocation == { "base", "f1", "f2", "f3", "f4", "f5", "f6", "r1", "r2", "b", "m" }

GroupLocation == { "toPlant", "planted", "toWater", "watered" }

Location == GroupLocation \union BaseLocation

SpaceEdge == { "se_0", "se_1", "se_2", "se_3", "se_4", "se_5", "se_6", "se_7", "se_8", "se_9", "se_10", "se_11", "se_12", "se_13", "se_14" }

SpaceSource ==
   "se_0" :> "base"
@@ "se_1" :> "f1"
@@ "se_2" :> "f1"
@@ "se_3" :> "f2"
@@ "se_4" :> "f2"
@@ "se_5" :> "f3"
@@ "se_6" :> "f2"
@@ "se_7" :> "b"
@@ "se_8" :> "f4"
@@ "se_9" :> "f5"
@@ "se_10" :> "f5"
@@ "se_11" :> "f6"
@@ "se_12" :> "f6"
@@ "se_13" :> "m"
@@ "se_14" :> "m"

SpaceTarget ==
   "se_0" :> "f1"
@@ "se_1" :> "base"
@@ "se_2" :> "f2"
@@ "se_3" :> "f1"
@@ "se_4" :> "f3"
@@ "se_5" :> "f2"
@@ "se_6" :> "b"
@@ "se_7" :> "f5"
@@ "se_8" :> "f5"
@@ "se_9" :> "f4"
@@ "se_10" :> "f6"
@@ "se_11" :> "f5"
@@ "se_12" :> "m"
@@ "se_13" :> "f6"
@@ "se_14" :> "f5"


Var == { "here", "_", "znc", "locControllerId", "locPlanterId" }

varloc ==
   "ControllerId" :> "locControllerId"
@@ "PlanterId" :> "locPlanterId"

locvar ==
   "locControllerId" :> "ControllerId"
@@ "locPlanterId" :> "PlanterId"

Reachable ==
   "base" :> { "b", "base", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f1" :> { "b", "base", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f2" :> { "b", "base", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f3" :> { "b", "base", "f1", "f2", "f3", "f4", "f5", "f6", "m" }
@@ "f4" :> { "f4", "f5", "f6", "m" }
@@ "f5" :> { "f4", "f5", "f6", "m" }
@@ "f6" :> { "f4", "f5", "f6", "m" }
@@ "r1" :> { "r1" }
@@ "r2" :> { "r2" }
@@ "b" :> { "b", "f4", "f5", "f6", "m" }
@@ "m" :> { "f4", "f5", "f6", "m" }

reachFrom(b) == UNION {Reachable[x] : x \in b}


cVar ==
   "Flow_0q7wp3m" :> "_"
@@ "Flow_10neqt1" :> "znc"
@@ "Flow_1skh2ra" :> "_"

cKind ==
   "Flow_0q7wp3m" :> Some
@@ "Flow_10neqt1" :> Some
@@ "Flow_1skh2ra" :> Some

cCond ==
   "Flow_0q7wp3m" :> "f_Flow_0q7wp3m"
@@ "Flow_10neqt1" :> "f_Flow_10neqt1"
@@ "Flow_1skh2ra" :> "f_Flow_1skh2ra"

def_f_Flow_0q7wp3m(v,s,p) == (v["znc"] \intersect reachFrom(v[varloc[p]]))

def_f_Flow_10neqt1(v,s,p) == s["toPlant"]

def_f_Flow_1skh2ra(v,s,p) == ({ "base" } \intersect reachFrom(v[varloc[p]]))



aKind ==
   "Activity_00galsb" :> Move
@@ "Activity_01kew4w" :> Pass
@@ "Activity_04y084u" :> Pass
@@ "Activity_0c215j4" :> Pass
@@ "Activity_0c5l85e" :> Pass
@@ "Activity_0qbls7q" :> Update
@@ "Activity_1xs44yy" :> Move













CodeCondition == { "f_Activity_00galsb", "f_Activity_1xs44yy", "f_Flow_0q7wp3m", "f_Flow_10neqt1", "f_Flow_1skh2ra" }

evalF(v,s,p,f) ==
IF f = "f_Activity_00galsb" THEN def_f_Activity_00galsb(v,s,p)
ELSE IF f = "f_Activity_1xs44yy" THEN def_f_Activity_1xs44yy(v,s,p)
ELSE IF f = "f_Flow_0q7wp3m" THEN def_f_Flow_0q7wp3m(v,s,p)
ELSE IF f = "f_Flow_10neqt1" THEN def_f_Flow_10neqt1(v,s,p)
ELSE IF f = "f_Flow_1skh2ra" THEN def_f_Flow_1skh2ra(v,s,p)
ELSE {  }

startloc ==
   "ControllerId" :> "base"
@@ "PlanterId" :> "base"

startsub ==
   "toPlant" :> { "f1", "f2", "f3", "f4", "f5", "f6" }
@@ "planted" :> {  }
@@ "toWater" :> {  }
@@ "watered" :> {  }



WF == INSTANCE PWSWellFormed
ASSUME WF!WellTyped
ASSUME WF!WellFormedness

ConstraintNode == TRUE \* none
ConstraintEdge == TRUE \* none
Constraint == TRUE     \* none
INSTANCE PWSConstraints

INSTANCE PWSSemantics

================================================================

