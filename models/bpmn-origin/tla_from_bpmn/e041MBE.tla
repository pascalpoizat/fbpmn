---------------- MODULE e041MBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Pid" :> { "interrupt", "info" }
  @@ "Qid" :> {  }

ContainRel ==
  "Pid" :> { "SubProcess_0gsfmc3", "InterruptBE", "StartEvent_1", "EndEvent_0rzkmq3", "BoundaryEvent_0ofx7yq", "NonInterruptBE", "BoundaryEvent_0lkn8pc", "EndEvent_08qbw2d", "EndEvent_086sfn7" }
  @@ "Qid" :> { "StartEvent_1s47y70", "ExclusiveGateway_0xuurqz", "EndEvent_14tvnqu", "SInfo", "ExclusiveGateway_1dkr7pq", "SInterrupt" }
  @@ "SubProcess_0gsfmc3" :> { "StartEvent_1wbfgbp", "TA", "EndEvent_009ffjw" }

Node == { "Pid", "Qid", "SubProcess_0gsfmc3", "InterruptBE", "StartEvent_1", "EndEvent_0rzkmq3", "BoundaryEvent_0ofx7yq", "NonInterruptBE", "BoundaryEvent_0lkn8pc", "EndEvent_08qbw2d", "EndEvent_086sfn7", "StartEvent_1wbfgbp", "TA", "EndEvent_009ffjw", "StartEvent_1s47y70", "ExclusiveGateway_0xuurqz", "EndEvent_14tvnqu", "SInfo", "ExclusiveGateway_1dkr7pq", "SInterrupt" }

Edge == { "MessageFlow_0vpnljc", "MessageFlow_12lpwl8", "SequenceFlow_1hkg88d", "SequenceFlow_1wjaklx", "SequenceFlow_0mtfqyq", "SequenceFlow_1qzgvib", "SequenceFlow_1uh9c90", "SequenceFlow_13lhzc9", "SequenceFlow_0zcc527", "SequenceFlow_0h86znt", "SequenceFlow_19yqu7y", "SequenceFlow_1sctg40", "SequenceFlow_1tf20c8", "SequenceFlow_1c63kjk", "SequenceFlow_0c9btso", "SequenceFlow_0v3rr2b" }

Message == { "interrupt", "info" }

msgtype ==
   "MessageFlow_0vpnljc" :> "interrupt"
@@ "MessageFlow_12lpwl8" :> "info"


source ==
   "MessageFlow_0vpnljc" :> "SInterrupt"
@@ "MessageFlow_12lpwl8" :> "SInfo"
@@ "SequenceFlow_1hkg88d" :> "StartEvent_1"
@@ "SequenceFlow_1wjaklx" :> "SubProcess_0gsfmc3"
@@ "SequenceFlow_0mtfqyq" :> "NonInterruptBE"
@@ "SequenceFlow_1qzgvib" :> "InterruptBE"
@@ "SequenceFlow_1uh9c90" :> "BoundaryEvent_0ofx7yq"
@@ "SequenceFlow_13lhzc9" :> "BoundaryEvent_0lkn8pc"
@@ "SequenceFlow_0zcc527" :> "StartEvent_1wbfgbp"
@@ "SequenceFlow_0h86znt" :> "TA"
@@ "SequenceFlow_19yqu7y" :> "StartEvent_1s47y70"
@@ "SequenceFlow_1sctg40" :> "ExclusiveGateway_0xuurqz"
@@ "SequenceFlow_1tf20c8" :> "ExclusiveGateway_0xuurqz"
@@ "SequenceFlow_1c63kjk" :> "SInterrupt"
@@ "SequenceFlow_0c9btso" :> "SInfo"
@@ "SequenceFlow_0v3rr2b" :> "ExclusiveGateway_1dkr7pq"

target ==
   "MessageFlow_0vpnljc" :> "InterruptBE"
@@ "MessageFlow_12lpwl8" :> "NonInterruptBE"
@@ "SequenceFlow_1hkg88d" :> "SubProcess_0gsfmc3"
@@ "SequenceFlow_1wjaklx" :> "EndEvent_0rzkmq3"
@@ "SequenceFlow_0mtfqyq" :> "EndEvent_08qbw2d"
@@ "SequenceFlow_1qzgvib" :> "EndEvent_086sfn7"
@@ "SequenceFlow_1uh9c90" :> "EndEvent_08qbw2d"
@@ "SequenceFlow_13lhzc9" :> "EndEvent_086sfn7"
@@ "SequenceFlow_0zcc527" :> "TA"
@@ "SequenceFlow_0h86znt" :> "EndEvent_009ffjw"
@@ "SequenceFlow_19yqu7y" :> "ExclusiveGateway_0xuurqz"
@@ "SequenceFlow_1sctg40" :> "SInterrupt"
@@ "SequenceFlow_1tf20c8" :> "SInfo"
@@ "SequenceFlow_1c63kjk" :> "ExclusiveGateway_1dkr7pq"
@@ "SequenceFlow_0c9btso" :> "ExclusiveGateway_1dkr7pq"
@@ "SequenceFlow_0v3rr2b" :> "EndEvent_14tvnqu"

CatN ==
   "Pid" :> Process
@@ "Qid" :> Process
@@ "SubProcess_0gsfmc3" :> SubProcess
@@ "InterruptBE" :> MessageBoundaryEvent
@@ "StartEvent_1" :> NoneStartEvent
@@ "EndEvent_0rzkmq3" :> NoneEndEvent
@@ "BoundaryEvent_0ofx7yq" :> TimerBoundaryEvent
@@ "NonInterruptBE" :> MessageBoundaryEvent
@@ "BoundaryEvent_0lkn8pc" :> TimerBoundaryEvent
@@ "EndEvent_08qbw2d" :> TerminateEndEvent
@@ "EndEvent_086sfn7" :> NoneEndEvent
@@ "StartEvent_1wbfgbp" :> NoneStartEvent
@@ "TA" :> AbstractTask
@@ "EndEvent_009ffjw" :> NoneEndEvent
@@ "StartEvent_1s47y70" :> NoneStartEvent
@@ "ExclusiveGateway_0xuurqz" :> ExclusiveOr
@@ "EndEvent_14tvnqu" :> NoneEndEvent
@@ "SInfo" :> SendTask
@@ "ExclusiveGateway_1dkr7pq" :> ExclusiveOr
@@ "SInterrupt" :> SendTask

CatE ==
   "MessageFlow_0vpnljc" :> MessageFlow
@@ "MessageFlow_12lpwl8" :> MessageFlow
@@ "SequenceFlow_1hkg88d" :> NormalSeqFlow
@@ "SequenceFlow_1wjaklx" :> NormalSeqFlow
@@ "SequenceFlow_0mtfqyq" :> NormalSeqFlow
@@ "SequenceFlow_1qzgvib" :> NormalSeqFlow
@@ "SequenceFlow_1uh9c90" :> NormalSeqFlow
@@ "SequenceFlow_13lhzc9" :> NormalSeqFlow
@@ "SequenceFlow_0zcc527" :> NormalSeqFlow
@@ "SequenceFlow_0h86znt" :> NormalSeqFlow
@@ "SequenceFlow_19yqu7y" :> NormalSeqFlow
@@ "SequenceFlow_1sctg40" :> NormalSeqFlow
@@ "SequenceFlow_1tf20c8" :> NormalSeqFlow
@@ "SequenceFlow_1c63kjk" :> NormalSeqFlow
@@ "SequenceFlow_0c9btso" :> NormalSeqFlow
@@ "SequenceFlow_0v3rr2b" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "InterruptBE" :> [ attachedTo |-> "SubProcess_0gsfmc3", cancelActivity |-> TRUE ]
@@ "NonInterruptBE" :> [ attachedTo |-> "SubProcess_0gsfmc3", cancelActivity |-> FALSE ]
@@ "BoundaryEvent_0ofx7yq" :> [ attachedTo |-> "SubProcess_0gsfmc3", cancelActivity |-> FALSE ]
@@ "BoundaryEvent_0lkn8pc" :> [ attachedTo |-> "SubProcess_0gsfmc3", cancelActivity |-> TRUE ]

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

