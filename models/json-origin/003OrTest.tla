---------------- MODULE 001OrTest ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process" :> { "NSE", "AT1", "Xor0", "Or1", "Xor1", "AT2", "Xor2", "AT3", "Or2", "AT4", "Xor3", "AT5", "NEE" }

Node == {
  "Process","NSE","AT1","Xor0","Or1","Xor1","AT2","Xor2","AT3","Or2","AT4","Xor3","AT5","NEE"
}

Edge == {
  "e0","e1","e2","e3","e4","e5","e6","e7","e8","e9","e10","e11","e12","e13","e14","e15"
}

Message == {  }

msgtype ==
      

source ==
   "e0" :> "NSE"
@@ "e1" :> "Xor0"
@@ "e2" :> "AT1"
@@ "e3" :> "Or1"
@@ "e4" :> "Or1"
@@ "e5" :> "AT3"
@@ "e6" :> "Xor1"
@@ "e7" :> "AT2"
@@ "e8" :> "Xor2"
@@ "e9" :> "Xor2"
@@ "e10" :> "Or2"
@@ "e11" :> "AT4"
@@ "e12" :> "Xor3"
@@ "e13" :> "Xor3"
@@ "e14" :> "AT5"
@@ "e15" :> "Or1"

target ==
   "e0" :> "Xor0"
@@ "e1" :> "AT1"
@@ "e2" :> "Or1"
@@ "e3" :> "Xor1"
@@ "e4" :> "AT3"
@@ "e5" :> "Or2"
@@ "e6" :> "AT2"
@@ "e7" :> "Xor2"
@@ "e8" :> "Xor1"
@@ "e9" :> "Or2"
@@ "e10" :> "AT4"
@@ "e11" :> "Xor3"
@@ "e12" :> "Or2"
@@ "e13" :> "AT5"
@@ "e14" :> "NEE"
@@ "e15" :> "Xor0"

CatN ==
   "Process" :> Process
@@ "NSE" :> NoneStartEvent
@@ "AT1" :> AbstractTask
@@ "Xor0" :> InclusiveOr
@@ "Or1" :> InclusiveOr
@@ "Xor1" :> ExclusiveOr
@@ "AT2" :> AbstractTask
@@ "Xor2" :> ExclusiveOr
@@ "AT3" :> AbstractTask
@@ "Or2" :> InclusiveOr
@@ "AT4" :> AbstractTask
@@ "Xor3" :> ExclusiveOr
@@ "AT5" :> AbstractTask
@@ "NEE" :> NoneEndEvent

CatE ==
   "e0" :> NormalSeqFlow
@@ "e1" :> NormalSeqFlow
@@ "e2" :> NormalSeqFlow
@@ "e3" :> NormalSeqFlow
@@ "e4" :> NormalSeqFlow
@@ "e5" :> NormalSeqFlow
@@ "e6" :> NormalSeqFlow
@@ "e7" :> NormalSeqFlow
@@ "e8" :> NormalSeqFlow
@@ "e9" :> NormalSeqFlow
@@ "e10" :> NormalSeqFlow
@@ "e11" :> NormalSeqFlow
@@ "e12" :> NormalSeqFlow
@@ "e13" :> NormalSeqFlow
@@ "e14" :> NormalSeqFlow
@@ "e15" :> NormalSeqFlow

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

