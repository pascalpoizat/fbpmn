---------------- MODULE 002ClientSupplierDynamic ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Client" :> { "cStart", "cEnd", "cSendCommand", "cStoreRequest", "cReceiveInvoice", "cReceiveGoods" }
  @@ "Supplier" :> { "sStart", "sPar1", "sPar2", "sEnd", "sPrepareCommand", "sInvoiceManagement", "sShipCommand", "sSendInvoice" }

Node == {
  "Supplier","sStart","sPar1","sPar2","sEnd","sPrepareCommand","sInvoiceManagement","sShipCommand","sSendInvoice","Client","cStart","cEnd","cSendCommand","cStoreRequest","cReceiveInvoice","cReceiveGoods"
}

Edge == {
  "sE1","sE2","sE3","sE4","sE5","sE6","sE7","sE8","cE1","cE2","cE3","cE4","cE5","mf1","mf2","mf3"
}

Message == { "command", "goods", "invoice" }

msgtype ==
      "mf1" :> "command"
  @@ "mf2" :> "invoice"
  @@ "mf3" :> "goods"

source ==
   "sE1" :> "sStart"
@@ "sE2" :> "sPar1"
@@ "sE3" :> "sPar1"
@@ "sE4" :> "sPrepareCommand"
@@ "sE5" :> "sInvoiceManagement"
@@ "sE6" :> "sPar2"
@@ "sE7" :> "sShipCommand"
@@ "sE8" :> "sSendInvoice"
@@ "cE1" :> "cStart"
@@ "cE2" :> "cSendCommand"
@@ "cE3" :> "cStoreRequest"
@@ "cE4" :> "cReceiveInvoice"
@@ "cE5" :> "cReceiveGoods"
@@ "mf1" :> "cSendCommand"
@@ "mf2" :> "sSendInvoice"
@@ "mf3" :> "sShipCommand"

target ==
   "sE1" :> "sPar1"
@@ "sE2" :> "sPrepareCommand"
@@ "sE3" :> "sInvoiceManagement"
@@ "sE4" :> "sPar2"
@@ "sE5" :> "sPar2"
@@ "sE6" :> "sShipCommand"
@@ "sE7" :> "sSendInvoice"
@@ "sE8" :> "sEnd"
@@ "cE1" :> "cSendCommand"
@@ "cE2" :> "cStoreRequest"
@@ "cE3" :> "cReceiveInvoice"
@@ "cE4" :> "cReceiveGoods"
@@ "cE5" :> "cEnd"
@@ "mf1" :> "sStart"
@@ "mf2" :> "cReceiveInvoice"
@@ "mf3" :> "cReceiveGoods"

CatN ==
   "Supplier" :> Process
@@ "sStart" :> MessageStartEvent
@@ "sPar1" :> Parallel
@@ "sPar2" :> Parallel
@@ "sEnd" :> NoneEndEvent
@@ "sPrepareCommand" :> AbstractTask
@@ "sInvoiceManagement" :> AbstractTask
@@ "sShipCommand" :> SendTask
@@ "sSendInvoice" :> SendTask
@@ "Client" :> Process
@@ "cStart" :> NoneStartEvent
@@ "cEnd" :> NoneEndEvent
@@ "cSendCommand" :> SendTask
@@ "cStoreRequest" :> AbstractTask
@@ "cReceiveInvoice" :> ReceiveTask
@@ "cReceiveGoods" :> ReceiveTask

CatE ==
   "sE1" :> NormalSeqFlow
@@ "sE2" :> NormalSeqFlow
@@ "sE3" :> NormalSeqFlow
@@ "sE4" :> NormalSeqFlow
@@ "sE5" :> NormalSeqFlow
@@ "sE6" :> NormalSeqFlow
@@ "sE7" :> NormalSeqFlow
@@ "sE8" :> NormalSeqFlow
@@ "cE1" :> NormalSeqFlow
@@ "cE2" :> NormalSeqFlow
@@ "cE3" :> NormalSeqFlow
@@ "cE4" :> NormalSeqFlow
@@ "cE5" :> NormalSeqFlow
@@ "mf1" :> MsgFlow
@@ "mf2" :> MsgFlow
@@ "mf3" :> MsgFlow

PreEdges ==
{}

PreNodes(n,e) == { target[ee] : ee \in PreEdges[n,e] }
          \union { nn \in { source[ee] : ee \in PreEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

