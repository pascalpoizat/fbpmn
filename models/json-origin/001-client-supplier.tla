---------------- MODULE 001-client-supplier ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

var == <<nodemarks, edgemarks, net>>

ContainRel ==
  "Client" :> { "cStart", "cEnd", "cSendCommand", "cStoreRequest", "cReceiveInvoice", "cReceiveGoods" }
  @@ "Supplier" :> { "sStart", "sPar1", "sPart2", "sEnd", "sReceiveCommand", "sPrepareCommand", "sInvoiceManagement", "sShipCommand", "sSendInvoice" }

Node == {
  "Supplier","sStart","sPar1","sPart2","sEnd","sReceiveCommand","sPrepareCommand","sInvoiceManagement","sShipCommand","sSendInvoice","Client","cStart","cEnd","cSendCommand","cStoreRequest","cReceiveInvoice","cReceiveGoods"
}

NormalSeqFlowEdge == {
  <<"sStart", "sReceiveCommand">>
  ,<<"sReceiveCommand", "sPar1">>
  ,<<"sPar1", "sPrepareCommand">>
  ,<<"sPar1", "sInvoiceManagement">>
  ,<<"sPrepareCommand", "sPar2">>
  ,<<"sInvoiceManagement", "sPar2">>
  ,<<"sPar2", "sShipCommand">>
  ,<<"sShipCommand", "sSendInvoice">>
  ,<<"sSendInvoice", "sEnd">>
  ,<<"cStart", "cSendCommand">>
  ,<<"cSendCommand", "cStoreRequest">>
  ,<<"sStoreRequest", "cReceiveInvoice">>
  ,<<"cReceiveInvoice", "cReceiveGoods">>
  ,<<"cReceiveGoods", "cEnd">>
}

MsgFlowEdge == {
  <<"cSendCommand", "sReceiveCommand">>
  ,<<"sSendInvoice", "cReceiveInvoice">>
  ,<<"sShipCommand", "cReceiveGoods">>
}

Edge == NormalSeqFlowEdge \union MsgFlowEdge

Message == { "command", "goods", "invoice" }

LOCAL msgtype0 ==
  "sShipCommand" :> { "goods" }
  @@ "sSendInvoice" :> { "invoice" }
  @@ "cSendCommand" :> { "command" }
  @@ "sReceiveCommand" :> { "command" }
  @@ "cReceiveInvoice" :> { "invoice" }
  @@ "cReceiveGoods" :> { "goods" }

msgtype == [ n \in Node |->
  IF n \in DOMAIN msgtype0 THEN msgtype0[n]
  ELSE {} ]

CatN ==
   "Supplier" :> Process
@@ "sStart" :> NoneStartEvent
@@ "sPar1" :> Parallel
@@ "sPart2" :> Parallel
@@ "sEnd" :> NoneEndEvent
@@ "sReceiveCommand" :> ReceiveTask
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

CatE == [ e \in Edge |->
            IF e \in NormalSeqFlowEdge THEN NormalSeqFlow
            ELSE MsgFlow
        ]

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

Spec == Init /\ [][Next]_var /\ WF_var(Next)

================================================================

