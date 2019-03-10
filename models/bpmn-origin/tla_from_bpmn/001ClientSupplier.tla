---------------- MODULE _001ClientSupplier ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_Client" :> { "cStart", "cSendCommand", "cEnd", "cReceiveInvoice", "cReceiveGoods", "cStoreRequest" }
  @@ "Process_Supplier" :> { "sStart", "sShipCommand", "sSendInvoice", "sReceiveCommand", "sInvoiceManagement", "sPrepareCommand", "sEnd", "sPar1", "sPar2" }

Node == {
  "Process_Supplier","Process_Client","sStart","sShipCommand","sSendInvoice","sReceiveCommand","sInvoiceManagement","sPrepareCommand","sEnd","sPar1","sPar2","cStart","cSendCommand","cEnd","cReceiveInvoice","cReceiveGoods","cStoreRequest"
}

Edge == {
  "mf1","mf3","mf2","sE1","sE2","sE3","sE4","sE5","sE6","sE7","sE8","sE9","cE1","cE2","cE3","cE4","cE5"
}

Message == { "command", "goods", "invoice" }

msgtype ==
      "mf1" :> "command"
  @@ "mf3" :> "goods"
  @@ "mf2" :> "invoice"

source ==
   "mf1" :> "cSendCommand"
@@ "mf3" :> "sShipCommand"
@@ "mf2" :> "sSendInvoice"
@@ "sE1" :> "sStart"
@@ "sE2" :> "sReceiveCommand"
@@ "sE3" :> "sPar1"
@@ "sE4" :> "sPar1"
@@ "sE5" :> "sPrepareCommand"
@@ "sE6" :> "sInvoiceManagement"
@@ "sE7" :> "sPar2"
@@ "sE8" :> "sShipCommand"
@@ "sE9" :> "sSendInvoice"
@@ "cE1" :> "cStart"
@@ "cE2" :> "cSendCommand"
@@ "cE3" :> "cStoreRequest"
@@ "cE4" :> "cReceiveInvoice"
@@ "cE5" :> "cReceiveGoods"

target ==
   "mf1" :> "sReceiveCommand"
@@ "mf3" :> "cReceiveGoods"
@@ "mf2" :> "cReceiveInvoice"
@@ "sE1" :> "sReceiveCommand"
@@ "sE2" :> "sPar1"
@@ "sE3" :> "sPrepareCommand"
@@ "sE4" :> "sInvoiceManagement"
@@ "sE5" :> "sPar2"
@@ "sE6" :> "sPar2"
@@ "sE7" :> "sShipCommand"
@@ "sE8" :> "sSendInvoice"
@@ "sE9" :> "sEnd"
@@ "cE1" :> "cSendCommand"
@@ "cE2" :> "cStoreRequest"
@@ "cE3" :> "cReceiveInvoice"
@@ "cE4" :> "cReceiveGoods"
@@ "cE5" :> "cEnd"

CatN ==
   "Process_Supplier" :> Process
@@ "Process_Client" :> Process
@@ "sStart" :> NoneStartEvent
@@ "sShipCommand" :> SendTask
@@ "sSendInvoice" :> SendTask
@@ "sReceiveCommand" :> ReceiveTask
@@ "sInvoiceManagement" :> AbstractTask
@@ "sPrepareCommand" :> AbstractTask
@@ "sEnd" :> NoneEndEvent
@@ "sPar1" :> Parallel
@@ "sPar2" :> Parallel
@@ "cStart" :> NoneStartEvent
@@ "cSendCommand" :> SendTask
@@ "cEnd" :> NoneEndEvent
@@ "cReceiveInvoice" :> ReceiveTask
@@ "cReceiveGoods" :> ReceiveTask
@@ "cStoreRequest" :> AbstractTask

CatE ==
   "mf1" :> MsgFlow
@@ "mf3" :> MsgFlow
@@ "mf2" :> MsgFlow
@@ "sE1" :> NormalSeqFlow
@@ "sE2" :> NormalSeqFlow
@@ "sE3" :> NormalSeqFlow
@@ "sE4" :> NormalSeqFlow
@@ "sE5" :> NormalSeqFlow
@@ "sE6" :> NormalSeqFlow
@@ "sE7" :> NormalSeqFlow
@@ "sE8" :> NormalSeqFlow
@@ "sE9" :> NormalSeqFlow
@@ "cE1" :> NormalSeqFlow
@@ "cE2" :> NormalSeqFlow
@@ "cE3" :> NormalSeqFlow
@@ "cE4" :> NormalSeqFlow
@@ "cE5" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

