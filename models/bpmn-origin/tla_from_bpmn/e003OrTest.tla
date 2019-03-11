---------------- MODULE e003OrTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_1" :> { "AT1", "Or1", "Xor1", "AT3", "AT2", "Xor2", "Or2", "Xor3", "AT4", "AT5", "NEE", "NSE", "Xor0" }

Node == {
  "Process_1","AT1","Or1","Xor1","AT3","AT2","Xor2","Or2","Xor3","AT4","AT5","NEE","NSE","Xor0"
}

Edge == {
  "e0","e2","e3","e4","e6","e7","e8","e9","e5","e10","e11","e12","e13","e14","e1","e15"
}

Message == {  }

msgtype ==
    [ i \in {} |-> {}]

source ==
   "e0" :> "NSE"
@@ "e2" :> "AT1"
@@ "e3" :> "Or1"
@@ "e4" :> "Or1"
@@ "e6" :> "Xor1"
@@ "e7" :> "AT2"
@@ "e8" :> "Xor2"
@@ "e9" :> "Xor2"
@@ "e5" :> "AT3"
@@ "e10" :> "Or2"
@@ "e11" :> "AT4"
@@ "e12" :> "Xor3"
@@ "e13" :> "Xor3"
@@ "e14" :> "AT5"
@@ "e1" :> "Xor0"
@@ "e15" :> "Or1"

target ==
   "e0" :> "Xor0"
@@ "e2" :> "Or1"
@@ "e3" :> "Xor1"
@@ "e4" :> "AT3"
@@ "e6" :> "AT2"
@@ "e7" :> "Xor2"
@@ "e8" :> "Xor1"
@@ "e9" :> "Or2"
@@ "e5" :> "Or2"
@@ "e10" :> "AT4"
@@ "e11" :> "Xor3"
@@ "e12" :> "Or2"
@@ "e13" :> "AT5"
@@ "e14" :> "NEE"
@@ "e1" :> "AT1"
@@ "e15" :> "Xor0"

CatN ==
   "Process_1" :> Process
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
   "e0" :> NormalSeqFlow
@@ "e2" :> NormalSeqFlow
@@ "e3" :> ConditionalSeqFlow
@@ "e4" :> ConditionalSeqFlow
@@ "e6" :> NormalSeqFlow
@@ "e7" :> NormalSeqFlow
@@ "e8" :> NormalSeqFlow
@@ "e9" :> ConditionalSeqFlow
@@ "e5" :> NormalSeqFlow
@@ "e10" :> NormalSeqFlow
@@ "e11" :> NormalSeqFlow
@@ "e12" :> NormalSeqFlow
@@ "e13" :> ConditionalSeqFlow
@@ "e14" :> NormalSeqFlow
@@ "e1" :> NormalSeqFlow
@@ "e15" :> NormalSeqFlow

LOCAL preEdges ==
<<"Or1", "e2">> :> {"e0", "e1", "e15"}
@@ <<"Or2", "e5">> :> {"e0", "e1", "e15", "e2", "e4"}
@@ <<"Or2", "e12">> :> {"e10", "e11"}
@@ <<"Or2", "e9">> :> {"e0", "e1", "e15", "e2", "e3", "e6", "e7", "e8"}
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

