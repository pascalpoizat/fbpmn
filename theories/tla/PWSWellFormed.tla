---------------- MODULE PWSWellFormed ----------------

EXTENDS PWSDefs, PWSTypes

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

----------------------------------------------------------------

(* Well-Structured BPMN Process Diagram *)

WSBPD_C1_StartNoIncomingEdge ==
    \A n \in Node : CatN[n] \in StartEventType => intype(SeqFlowType,n) = {}

WSBPD_C2_EndNoOutgoingEdge ==
    \A n \in Node : CatN[n] \in EndEventType => outtype(SeqFlowType,n) = {}

WSBPD_C3_SubProcessUniqueStart ==
    \A n \in Node : CatN[n] = SubProcess => Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType }) = 1

WSBPD_C4_NoProcessInSubProcess ==
    \A n \in Node : CatN[n] = SubProcess => \A nn \in ContainRel[n] : CatN[nn] # Process

WellStructuredBPD == /\ WSBPD_C1_StartNoIncomingEdge
                     /\ WSBPD_C2_EndNoOutgoingEdge
                     /\ WSBPD_C3_SubProcessUniqueStart
                     /\ WSBPD_C4_NoProcessInSubProcess

----------------------------------------------------------------

(* Well-Formed BPMN Process Diagram *)

WFBPD_C1_NoLoopingEdge ==
    \A e \in Edge : source(e) # target(e)

WFBPD_C2_NotIsolation ==
    \A n \in Node : CatN[n] # Process => incoming(n) # {} \/ outgoing(n) # {}

WFBPD_C3_DefaultSeqFlow ==
    \A n \in Node : CatN[n] \in {ExclusiveOr, InclusiveOr} => Cardinality(intype({ConditionalSeqFlow},n)) >= 1 /\ Cardinality(outtype({DefaultSeqFlow},n)) = 1

WellFormednessBPD == /\ WFBPD_C1_NoLoopingEdge
                     /\ WFBPD_C2_NotIsolation
                     /\ WFBPD_C3_DefaultSeqFlow

----------------------------------------------------------------

(* Well-Structured BPMN Collaboration Diagram *)

WSBCD_C1_SendTask ==
    \A n \in Node : CatN[n] = SendTask => intype(MsgFlowType,n) = {}

WSBCD_C2_ReceiveTask ==
    \A n \in Node : CatN[n] = ReceiveTask => outtype(MsgFlowType,n) = {}

WSBCD_C3_MessageFlowDifferentProcesses ==
    \A ni, nj \in Processes, e \in Edge : CatE[e] \in MsgFlowType /\ source(e) \in ContainRel[ni] /\ target(e) \in ContainRel[nj] => ni # nj

(*
WSBCD_Cx_MessageFlowEdge ==
    \A e \in Edge : CatE[e] = MsgFlow <=> (CatN[source(e)] = SendTask /\ CatN[target(e)] = ReceiveTask)
*)

WellStructuredBCD == /\ WSBCD_C1_SendTask
                     /\ WSBCD_C2_ReceiveTask
                     /\ WSBCD_C3_MessageFlowDifferentProcesses

----------------------------------------------------------------

WellFormedness == TypeAssume /\ WellStructuredBPD /\ WellFormednessBPD /\ WellStructuredBCD

================================================================
