---------------- MODULE eXXX_TICEDuration ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Pid" :> {  }

ContainRel ==
  "Pid" :> { "ee", "ti", "se" }

Node == { "Pid", "ee", "ti", "se" }

Edge == { "SequenceFlow_04jhviy", "SequenceFlow_0b689qw" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_04jhviy" :> "se"
@@ "SequenceFlow_0b689qw" :> "ti"

target ==
   "SequenceFlow_04jhviy" :> "ti"
@@ "SequenceFlow_0b689qw" :> "ee"

CatN ==
   "Pid" :> Process
@@ "ee" :> NoneEndEvent
@@ "ti" :> TimerIntermediateEvent
@@ "se" :> NoneStartEvent

CatE ==
   "SequenceFlow_04jhviy" :> NormalSeqFlow
@@ "SequenceFlow_0b689qw" :> NormalSeqFlow

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

