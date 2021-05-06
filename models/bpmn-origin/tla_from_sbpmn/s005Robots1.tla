---------------- MODULE s005Robots1 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net, subs, sigma

Interest ==
  "ControllerId" :> {  }
  @@ "RobotId" :> { "order_move_Z1", "order_move_Z2" }

ContainRel ==
  "ControllerId" :> { "StartEvent_1", "Gateway_06tqqfq", "Activity_0wyc0k0", "Activity_1v25x1v", "Event_1o9zl5p", "Activity_036473v" }
  @@ "RobotId" :> { "Event_0m2ahyx", "Gateway_09tktio", "Event_0913gwy", "Event_1w6u3rw", "Event_0nzpc9u", "Activity_0cl1ijx", "Activity_1oht5l5", "Event_0mkdyfd" }

Node == { "ControllerId", "RobotId", "StartEvent_1", "Gateway_06tqqfq", "Activity_0wyc0k0", "Activity_1v25x1v", "Event_1o9zl5p", "Activity_036473v", "Event_0m2ahyx", "Gateway_09tktio", "Event_0913gwy", "Event_1w6u3rw", "Event_0nzpc9u", "Activity_0cl1ijx", "Activity_1oht5l5", "Event_0mkdyfd" }

Edge == { "Flow_01got9k", "Flow_1fv8z4y", "Flow_0j10pgk", "Flow_0a9bfn5", "Flow_1a846z9", "Flow_122malt", "Flow_118xc7r", "Flow_0ix38zj", "Flow_0ixsr65", "Flow_12l0eds", "Flow_1prda8c", "Flow_0u8jw5x", "Flow_1e3vt40", "Flow_0sbmxh0", "Flow_0qcjodn", "Flow_1ku1tkz" }

Message == { "order_move_Z1", "order_move_Z2" }

msgtype ==
   "Flow_01got9k" :> "order_move_Z1"
@@ "Flow_1fv8z4y" :> "order_move_Z2"


source ==
   "Flow_01got9k" :> "Activity_0wyc0k0"
@@ "Flow_1fv8z4y" :> "Activity_1v25x1v"
@@ "Flow_0j10pgk" :> "Gateway_06tqqfq"
@@ "Flow_0a9bfn5" :> "Gateway_06tqqfq"
@@ "Flow_1a846z9" :> "Activity_0wyc0k0"
@@ "Flow_122malt" :> "Activity_1v25x1v"
@@ "Flow_118xc7r" :> "Gateway_06tqqfq"
@@ "Flow_0ix38zj" :> "StartEvent_1"
@@ "Flow_0ixsr65" :> "Activity_036473v"
@@ "Flow_12l0eds" :> "Activity_0cl1ijx"
@@ "Flow_1prda8c" :> "Activity_1oht5l5"
@@ "Flow_0u8jw5x" :> "Event_0913gwy"
@@ "Flow_1e3vt40" :> "Gateway_09tktio"
@@ "Flow_0sbmxh0" :> "Gateway_09tktio"
@@ "Flow_0qcjodn" :> "Event_0m2ahyx"
@@ "Flow_1ku1tkz" :> "Event_0mkdyfd"

target ==
   "Flow_01got9k" :> "Event_0m2ahyx"
@@ "Flow_1fv8z4y" :> "Event_0mkdyfd"
@@ "Flow_0j10pgk" :> "Activity_0wyc0k0"
@@ "Flow_0a9bfn5" :> "Activity_1v25x1v"
@@ "Flow_1a846z9" :> "Event_1o9zl5p"
@@ "Flow_122malt" :> "Event_1o9zl5p"
@@ "Flow_118xc7r" :> "Activity_036473v"
@@ "Flow_0ix38zj" :> "Gateway_06tqqfq"
@@ "Flow_0ixsr65" :> "Event_1o9zl5p"
@@ "Flow_12l0eds" :> "Event_1w6u3rw"
@@ "Flow_1prda8c" :> "Event_0nzpc9u"
@@ "Flow_0u8jw5x" :> "Gateway_09tktio"
@@ "Flow_1e3vt40" :> "Event_0m2ahyx"
@@ "Flow_0sbmxh0" :> "Event_0mkdyfd"
@@ "Flow_0qcjodn" :> "Activity_0cl1ijx"
@@ "Flow_1ku1tkz" :> "Activity_1oht5l5"

CatN ==
   "ControllerId" :> Process
@@ "RobotId" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Gateway_06tqqfq" :> ExclusiveOr
@@ "Activity_0wyc0k0" :> SendTask
@@ "Activity_1v25x1v" :> SendTask
@@ "Event_1o9zl5p" :> NoneEndEvent
@@ "Activity_036473v" :> AbstractTask
@@ "Event_0m2ahyx" :> CatchMessageIntermediateEvent
@@ "Gateway_09tktio" :> EventBased
@@ "Event_0913gwy" :> NoneStartEvent
@@ "Event_1w6u3rw" :> NoneEndEvent
@@ "Event_0nzpc9u" :> NoneEndEvent
@@ "Activity_0cl1ijx" :> AbstractTask
@@ "Activity_1oht5l5" :> AbstractTask
@@ "Event_0mkdyfd" :> CatchMessageIntermediateEvent

CatE ==
   "Flow_01got9k" :> MessageFlow
@@ "Flow_1fv8z4y" :> MessageFlow
@@ "Flow_0j10pgk" :> ConditionalSeqFlow
@@ "Flow_0a9bfn5" :> ConditionalSeqFlow
@@ "Flow_1a846z9" :> NormalSeqFlow
@@ "Flow_122malt" :> NormalSeqFlow
@@ "Flow_118xc7r" :> DefaultSeqFlow
@@ "Flow_0ix38zj" :> NormalSeqFlow
@@ "Flow_0ixsr65" :> NormalSeqFlow
@@ "Flow_12l0eds" :> NormalSeqFlow
@@ "Flow_1prda8c" :> NormalSeqFlow
@@ "Flow_0u8jw5x" :> NormalSeqFlow
@@ "Flow_1e3vt40" :> NormalSeqFlow
@@ "Flow_0sbmxh0" :> NormalSeqFlow
@@ "Flow_0qcjodn" :> NormalSeqFlow
@@ "Flow_1ku1tkz" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
  [ i \in {} |-> {}]

BaseLocation == { "z0", "z1", "z2" }

GroupLocation == { "Z1", "Z2" }

Location == GroupLocation \union BaseLocation

SpaceEdge == { "se_0", "se_1" }

SpaceSource ==
   "se_0" :> "z0"
@@ "se_1" :> "z0"

SpaceTarget ==
   "se_0" :> "z1"
@@ "se_1" :> "z2"


Var == { "here", "_", "locControllerId", "locRobotId" }

varloc ==
   "ControllerId" :> "locControllerId"
@@ "RobotId" :> "locRobotId"

locvar ==
   "locControllerId" :> "ControllerId"
@@ "locRobotId" :> "RobotId"

Reachable ==
   "z0" :> { "z0", "z1", "z2" }
@@ "z1" :> { "z1" }
@@ "z2" :> { "z2" }

reachFrom(b) == UNION {Reachable[x] : x \in b}


cVar ==
   "Flow_0a9bfn5" :> "_"
@@ "Flow_0j10pgk" :> "_"

cKind ==
   "Flow_0a9bfn5" :> Some
@@ "Flow_0j10pgk" :> Some

cCond ==
   "Flow_0a9bfn5" :> "f_Flow_0a9bfn5"
@@ "Flow_0j10pgk" :> "f_Flow_0j10pgk"

def_f_Flow_0a9bfn5(v,s,p) == (reachFrom(v[varloc[p]]) \intersect s["Z2"])

def_f_Flow_0j10pgk(v,s,p) == (reachFrom(v[varloc[p]]) \intersect s["Z1"])


orderingSet == { }
order(a,b) == <<a,b>> \in orderingSet


aKind ==
   "Activity_036473v" :> ACT_PASS
@@ "Activity_0cl1ijx" :> ACT_MOVE
@@ "Activity_1oht5l5" :> ACT_MOVE

aUpdateVar ==
  [ i \in {} |-> {}]

aUpdateGMinus ==
  [ i \in {} |-> {}]

aUpdateGPlus ==
  [ i \in {} |-> {}]

aCond ==
   "Activity_0cl1ijx" :> "f_Activity_0cl1ijx"
@@ "Activity_1oht5l5" :> "f_Activity_1oht5l5"

def_f_Activity_0cl1ijx(v,s,p) == s["Z1"]

def_f_Activity_1oht5l5(v,s,p) == s["Z2"]



CodeCondition == { "f_Activity_0cl1ijx", "f_Activity_1oht5l5", "f_Flow_0a9bfn5", "f_Flow_0j10pgk" }

evalF(v,s,p,f) ==
IF f = "f_Activity_0cl1ijx" THEN def_f_Activity_0cl1ijx(v,s,p)
ELSE IF f = "f_Activity_1oht5l5" THEN def_f_Activity_1oht5l5(v,s,p)
ELSE IF f = "f_Flow_0a9bfn5" THEN def_f_Flow_0a9bfn5(v,s,p)
ELSE IF f = "f_Flow_0j10pgk" THEN def_f_Flow_0j10pgk(v,s,p)
ELSE {  }

startloc ==
   "ControllerId" :> "z0"
@@ "RobotId" :> "z0"

startsub ==
   "Z1" :> { "z1" }
@@ "Z2" :> { "z2" }



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

