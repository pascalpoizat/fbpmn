---------------- MODULE s010ConditionOrdering ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net
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
   "Flow_09a8um7" :> "StartEvent_1"@@ "flow_to_f2" :> "xor"@@ "default_flow" :> "xor"@@ "flow_to_f3" :> "xor"@@ "Flow_1bc6u3c" :> "Activity_071wli2"@@ "Flow_1ddop94" :> "Activity_18vh6pp"
target ==
   "Flow_09a8um7" :> "xor"@@ "flow_to_f2" :> "Activity_071wli2"@@ "default_flow" :> "endInPlace"@@ "flow_to_f3" :> "Activity_18vh6pp"@@ "Flow_1bc6u3c" :> "endF2"@@ "Flow_1ddop94" :> "endF3"
CatN ==
   "PId" :> Process@@ "endF2" :> NoneEndEvent@@ "endInPlace" :> NoneEndEvent@@ "endF3" :> NoneEndEvent@@ "xor" :> ExclusiveOr@@ "StartEvent_1" :> NoneStartEvent@@ "Activity_071wli2" :> AbstractTask@@ "Activity_18vh6pp" :> AbstractTask
CatE ==
   "Flow_09a8um7" :> NormalSeqFlow@@ "flow_to_f2" :> ConditionalSeqFlow@@ "default_flow" :> DefaultSeqFlow@@ "flow_to_f3" :> ConditionalSeqFlow@@ "Flow_1bc6u3c" :> NormalSeqFlow@@ "Flow_1ddop94" :> NormalSeqFlow
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
