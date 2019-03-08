---------------- MODULE 006TravelAgency ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Customer" :> { "n1", "n2", "n3", "n4", "n5", "n6", "n7", "n8", "n9" }
  @@ "TravelAgency" :> { "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9" }

Node == {
  "Customer","n1","n2","n3","n4","n5","n6","n7","n8","n9","TravelAgency","t1","t2","t3","t4","t5","t6","t7","t8","t9"
}

Edge == {
  "e1","e2","e3","e4","e5","e6","e7","e8","e9","f1","f2","f3","f4","f5","f6","f7","f8","f9","mf1","mf2","mf3","mf4","mf5"
}

Message == { "Offer", "Travel", "Payment", "Confirmation", "Ticket" }

msgtype ==
      "mf1" :> "Offer"
  @@ "mf2" :> "Travel"
  @@ "mf3" :> "Payment"
  @@ "mf4" :> "Confirmation"
  @@ "mf5" :> "Ticket"

source ==
   "e1" :> "n1"
@@ "e2" :> "n2"
@@ "e3" :> "n3"
@@ "e4" :> "n4"
@@ "e5" :> "n4"
@@ "e6" :> "n5"
@@ "e7" :> "n6"
@@ "e8" :> "n7"
@@ "e9" :> "n8"
@@ "f1" :> "t1"
@@ "f2" :> "t2"
@@ "f3" :> "t3"
@@ "f4" :> "t4"
@@ "f5" :> "t4"
@@ "f6" :> "t5"
@@ "f7" :> "t6"
@@ "f8" :> "t7"
@@ "f9" :> "t8"
@@ "mf1" :> "t3"
@@ "mf2" :> "n5"
@@ "mf3" :> "n6"
@@ "mf4" :> "t7"
@@ "mf5" :> "t8"

target ==
   "e1" :> "n2"
@@ "e2" :> "n3"
@@ "e3" :> "n4"
@@ "e4" :> "n2"
@@ "e5" :> "n5"
@@ "e6" :> "n6"
@@ "e7" :> "n7"
@@ "e8" :> "n8"
@@ "e9" :> "n9"
@@ "f1" :> "t2"
@@ "f2" :> "t3"
@@ "f3" :> "t4"
@@ "f4" :> "t2"
@@ "f5" :> "t5"
@@ "f6" :> "t6"
@@ "f7" :> "t7"
@@ "f8" :> "t8"
@@ "f9" :> "t9"
@@ "mf1" :> "n3"
@@ "mf2" :> "t5"
@@ "mf3" :> "t6"
@@ "mf4" :> "n8"
@@ "mf5" :> "n7"

CatN ==
   "Customer" :> Process
@@ "n1" :> NoneStartEvent
@@ "n2" :> ExclusiveOr
@@ "n3" :> ReceiveTask
@@ "n4" :> ExclusiveOr
@@ "n5" :> SendTask
@@ "n6" :> SendTask
@@ "n7" :> CatchMessageIntermediateEvent
@@ "n8" :> CatchMessageIntermediateEvent
@@ "n9" :> NoneEndEvent
@@ "TravelAgency" :> Process
@@ "t1" :> NoneStartEvent
@@ "t2" :> ExclusiveOr
@@ "t3" :> SendTask
@@ "t4" :> Parallel
@@ "t5" :> CatchMessageIntermediateEvent
@@ "t6" :> CatchMessageIntermediateEvent
@@ "t7" :> SendTask
@@ "t8" :> SendTask
@@ "t9" :> TerminateEndEvent

CatE ==
   "e1" :> NormalSeqFlow
@@ "e2" :> NormalSeqFlow
@@ "e3" :> NormalSeqFlow
@@ "e4" :> NormalSeqFlow
@@ "e5" :> NormalSeqFlow
@@ "e6" :> NormalSeqFlow
@@ "e7" :> NormalSeqFlow
@@ "e8" :> NormalSeqFlow
@@ "e9" :> NormalSeqFlow
@@ "f1" :> NormalSeqFlow
@@ "f2" :> NormalSeqFlow
@@ "f3" :> NormalSeqFlow
@@ "f4" :> NormalSeqFlow
@@ "f5" :> NormalSeqFlow
@@ "f6" :> NormalSeqFlow
@@ "f7" :> NormalSeqFlow
@@ "f8" :> NormalSeqFlow
@@ "f9" :> NormalSeqFlow
@@ "mf1" :> MsgFlow
@@ "mf2" :> MsgFlow
@@ "mf3" :> MsgFlow
@@ "mf4" :> MsgFlow
@@ "mf5" :> MsgFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

