---------------- MODULE e003OrTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Process_" :> {  }

ContainRel ==
  "Process_" :> { "AT1", "Or1", "Xor1", "AT3", "AT2", "Xor2", "Or2", "Xor3", "AT4", "AT5", "NEE", "NSE", "Xor0" }

Node == { "Process_", "AT1", "Or1", "Xor1", "AT3", "AT2", "Xor2", "Or2", "Xor3", "AT4", "AT5", "NEE", "NSE", "Xor0" }

Edge == { "e15", "e1", "e14", "e13", "e12", "e11", "e10", "e5", "e9", "e8", "e7", "e6", "e4", "e3", "e2", "e0" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "e15" :> "Or1"
@@ "e1" :> "Xor0"
@@ "e14" :> "AT5"
@@ "e13" :> "Xor3"
@@ "e12" :> "Xor3"
@@ "e11" :> "AT4"
@@ "e10" :> "Or2"
@@ "e5" :> "AT3"
@@ "e9" :> "Xor2"
@@ "e8" :> "Xor2"
@@ "e7" :> "AT2"
@@ "e6" :> "Xor1"
@@ "e4" :> "Or1"
@@ "e3" :> "Or1"
@@ "e2" :> "AT1"
@@ "e0" :> "NSE"

target ==
   "e15" :> "Xor0"
@@ "e1" :> "AT1"
@@ "e14" :> "NEE"
@@ "e13" :> "AT5"
@@ "e12" :> "Or2"
@@ "e11" :> "Xor3"
@@ "e10" :> "AT4"
@@ "e5" :> "Or2"
@@ "e9" :> "Or2"
@@ "e8" :> "Xor1"
@@ "e7" :> "Xor2"
@@ "e6" :> "AT2"
@@ "e4" :> "AT3"
@@ "e3" :> "Xor1"
@@ "e2" :> "Or1"
@@ "e0" :> "Xor0"

CatN ==
   "Process_" :> Process
@@ "AT1" :> AbstractTask
@@ "Or1" :> InclusiveOr
@@ "Xor1" :> ExclusiveOr
@@ "AT3" :> AbstractTask
@@ "AT2" :> AbstractTask
@@ "Xor2" :> ExclusiveOr
@@ "Or2" :> InclusiveOr
@@ "Xor3" :> ExclusiveOr
@@ "AT4" :> AbstractTask
@@ "AT5" :> AbstractTask
@@ "NEE" :> NoneEndEvent
@@ "NSE" :> NoneStartEvent
@@ "Xor0" :> ExclusiveOr

CatE ==
   "e15" :> DefaultSeqFlow
@@ "e1" :> NormalSeqFlow
@@ "e14" :> NormalSeqFlow
@@ "e13" :> ConditionalSeqFlow
@@ "e12" :> DefaultSeqFlow
@@ "e11" :> NormalSeqFlow
@@ "e10" :> NormalSeqFlow
@@ "e5" :> NormalSeqFlow
@@ "e9" :> ConditionalSeqFlow
@@ "e8" :> DefaultSeqFlow
@@ "e7" :> NormalSeqFlow
@@ "e6" :> NormalSeqFlow
@@ "e4" :> ConditionalSeqFlow
@@ "e3" :> ConditionalSeqFlow
@@ "e2" :> NormalSeqFlow
@@ "e0" :> NormalSeqFlow

LOCAL preEdges ==
   <<"Or1", "e2">> :> {"e0", "e1", "e15"}
@@ <<"Or2", "e5">> :> {"e0", "e1", "e15", "e2", "e4"}
@@ <<"Or2", "e9">> :> {"e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"}
@@ <<"Or2", "e12">> :> {"e10", "e11"}
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

