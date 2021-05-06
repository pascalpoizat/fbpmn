---------------- MODULE e054TEB ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "A_" :> {  }
  @@ "B_" :> { "m1", "m2" }
  @@ "C_" :> {  }

ContainRel ==
  "A_" :> { "A_EE2", "A_T", "A_NSE", "A_XOR", "A_EE1", "A_ST" }
  @@ "B_" :> { "B_NSE", "B_EB", "B_MICE1", "B_MICE2", "B_TIE", "B_EE1", "B_EE2", "B_EE3" }
  @@ "C_" :> { "C_NSE", "C_XOR", "C_EE2", "C_EE1", "C_T", "C_ST" }

Node == { "B_", "C_", "A_", "B_NSE", "B_EB", "B_MICE1", "B_MICE2", "B_TIE", "B_EE1", "B_EE2", "B_EE3", "C_NSE", "C_XOR", "C_EE2", "C_EE1", "C_T", "C_ST", "A_EE2", "A_T", "A_NSE", "A_XOR", "A_EE1", "A_ST" }

Edge == { "MessageFlow_0anis1g", "MessageFlow_0mma6b7", "SequenceFlow_1kqxai7", "SequenceFlow_1w1q1tz", "SequenceFlow_01mi0z5", "SequenceFlow_0d4uo9u", "SequenceFlow_1lim0ak", "SequenceFlow_1ejcjun", "SequenceFlow_02i9aub", "SequenceFlow_0062gga", "SequenceFlow_1fpdtzj", "SequenceFlow_0m6s08w", "SequenceFlow_1jusdil", "SequenceFlow_0sz8f29", "SequenceFlow_13q04ef", "SequenceFlow_1jbid03", "SequenceFlow_1qj818y", "SequenceFlow_1lmhnxh", "SequenceFlow_11z8969" }

Message == { "m1", "m2" }

msgtype ==
   "MessageFlow_0anis1g" :> "m1"
@@ "MessageFlow_0mma6b7" :> "m2"


source ==
   "MessageFlow_0anis1g" :> "A_ST"
@@ "MessageFlow_0mma6b7" :> "C_ST"
@@ "SequenceFlow_1kqxai7" :> "B_TIE"
@@ "SequenceFlow_1w1q1tz" :> "B_MICE2"
@@ "SequenceFlow_01mi0z5" :> "B_MICE1"
@@ "SequenceFlow_0d4uo9u" :> "B_EB"
@@ "SequenceFlow_1lim0ak" :> "B_EB"
@@ "SequenceFlow_1ejcjun" :> "B_EB"
@@ "SequenceFlow_02i9aub" :> "B_NSE"
@@ "SequenceFlow_0062gga" :> "C_NSE"
@@ "SequenceFlow_1fpdtzj" :> "C_XOR"
@@ "SequenceFlow_0m6s08w" :> "C_XOR"
@@ "SequenceFlow_1jusdil" :> "C_T"
@@ "SequenceFlow_0sz8f29" :> "C_ST"
@@ "SequenceFlow_13q04ef" :> "A_XOR"
@@ "SequenceFlow_1jbid03" :> "A_ST"
@@ "SequenceFlow_1qj818y" :> "A_XOR"
@@ "SequenceFlow_1lmhnxh" :> "A_NSE"
@@ "SequenceFlow_11z8969" :> "A_T"

target ==
   "MessageFlow_0anis1g" :> "B_MICE1"
@@ "MessageFlow_0mma6b7" :> "B_MICE2"
@@ "SequenceFlow_1kqxai7" :> "B_EE3"
@@ "SequenceFlow_1w1q1tz" :> "B_EE2"
@@ "SequenceFlow_01mi0z5" :> "B_EE1"
@@ "SequenceFlow_0d4uo9u" :> "B_TIE"
@@ "SequenceFlow_1lim0ak" :> "B_MICE2"
@@ "SequenceFlow_1ejcjun" :> "B_MICE1"
@@ "SequenceFlow_02i9aub" :> "B_EB"
@@ "SequenceFlow_0062gga" :> "C_XOR"
@@ "SequenceFlow_1fpdtzj" :> "C_T"
@@ "SequenceFlow_0m6s08w" :> "C_ST"
@@ "SequenceFlow_1jusdil" :> "C_EE2"
@@ "SequenceFlow_0sz8f29" :> "C_EE1"
@@ "SequenceFlow_13q04ef" :> "A_ST"
@@ "SequenceFlow_1jbid03" :> "A_EE2"
@@ "SequenceFlow_1qj818y" :> "A_T"
@@ "SequenceFlow_1lmhnxh" :> "A_XOR"
@@ "SequenceFlow_11z8969" :> "A_EE1"

CatN ==
   "B_" :> Process
@@ "C_" :> Process
@@ "A_" :> Process
@@ "B_NSE" :> NoneStartEvent
@@ "B_EB" :> EventBased
@@ "B_MICE1" :> CatchMessageIntermediateEvent
@@ "B_MICE2" :> CatchMessageIntermediateEvent
@@ "B_TIE" :> TimerIntermediateEvent
@@ "B_EE1" :> NoneEndEvent
@@ "B_EE2" :> NoneEndEvent
@@ "B_EE3" :> NoneEndEvent
@@ "C_NSE" :> NoneStartEvent
@@ "C_XOR" :> ExclusiveOr
@@ "C_EE2" :> NoneEndEvent
@@ "C_EE1" :> NoneEndEvent
@@ "C_T" :> AbstractTask
@@ "C_ST" :> SendTask
@@ "A_EE2" :> NoneEndEvent
@@ "A_T" :> AbstractTask
@@ "A_NSE" :> NoneStartEvent
@@ "A_XOR" :> ExclusiveOr
@@ "A_EE1" :> NoneEndEvent
@@ "A_ST" :> SendTask

CatE ==
   "MessageFlow_0anis1g" :> MessageFlow
@@ "MessageFlow_0mma6b7" :> MessageFlow
@@ "SequenceFlow_1kqxai7" :> NormalSeqFlow
@@ "SequenceFlow_1w1q1tz" :> NormalSeqFlow
@@ "SequenceFlow_01mi0z5" :> NormalSeqFlow
@@ "SequenceFlow_0d4uo9u" :> NormalSeqFlow
@@ "SequenceFlow_1lim0ak" :> NormalSeqFlow
@@ "SequenceFlow_1ejcjun" :> NormalSeqFlow
@@ "SequenceFlow_02i9aub" :> NormalSeqFlow
@@ "SequenceFlow_0062gga" :> NormalSeqFlow
@@ "SequenceFlow_1fpdtzj" :> NormalSeqFlow
@@ "SequenceFlow_0m6s08w" :> NormalSeqFlow
@@ "SequenceFlow_1jusdil" :> NormalSeqFlow
@@ "SequenceFlow_0sz8f29" :> NormalSeqFlow
@@ "SequenceFlow_13q04ef" :> NormalSeqFlow
@@ "SequenceFlow_1jbid03" :> NormalSeqFlow
@@ "SequenceFlow_1qj818y" :> NormalSeqFlow
@@ "SequenceFlow_1lmhnxh" :> NormalSeqFlow
@@ "SequenceFlow_11z8969" :> NormalSeqFlow

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

