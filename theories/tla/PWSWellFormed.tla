---------------- MODULE PWSWellFormed ----------------
(* Rules of well-structureness *)

EXTENDS PWSDefs, PWSTypes

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

----------------------------------------------------------------

C1_StartNoIncomingEdge ==
    \A n \in Node : CatN[n] \in StartEventType => intype(SeqFlowType,n) = {}

C2_EndNoOutgoingEdge ==
    \A n \in Node : CatN[n] \in EndEventType => outtype(SeqFlowType,n) = {}

C3_SubProcessUniqueStart ==
    \A n \in Node : CatN[n] = SubProcess => Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType }) = 1

C4_NoProcessInSubProcess ==
    \A n \in Node : CatN[n] = SubProcess => \A nn \in ContainRel[n] : CatN[nn] # Process

C5_ProcessNode ==
    \A n \in Node : CatN[n] = Process =>
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType } # {}
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in EndEventType } # {}
    \* /\ Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] = Process }) = 1 \* impossible

C6_NoLoopingEdge ==
    \A e \in Edge : source[e] # target[e]

C7_NotIsolation ==
    \A n \in Node : (CatN[n] # Process /\ CatN[n] # MessageBoundaryEvent) => incoming(n) # {} \/ outgoing(n) # {}

C8_DefaultSeqFlow == \* A gateway that has a conditional edge must have a default edge.
    \A n \in Node : CatN[n] \in GatewayType /\ outtype({ConditionalSeqFlow},n) # {} => Cardinality(outtype({DefaultSeqFlow},n)) = 1

C9_SendTask ==
    \A n \in Node : CatN[n] = SendTask => intype(MessageFlowType,n) = {}

C10_ReceiveTask ==
    \A n \in Node : CatN[n] = ReceiveTask => outtype(MessageFlowType,n) = {}

C11_MessageFlowDifferentProcesses ==
    \A ni, nj \in Processes, e \in Edge : CatE[e] \in MessageFlowType /\ source[e] \in ContainRel[ni] /\ target[e] \in ContainRel[nj] => ni # nj

C12_EXORTwoOutgoingEdges ==
    \A n \in Node : CatN[n] = EventBased => Cardinality(outtype(SeqFlowType, n)) >= 2

C13_EXOR_NoConditional ==
    \A n \in Node : CatN[n] = EventBased => outtype({ConditionalSeqFlow}, n) = {}

C14_EXOR_NextElements ==
    \A n \in Node : CatN[n] = EventBased =>
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] = ReceiveTask
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] = CatchMessageIntermediateEvent

(*
Cx_MessageFlowEdge ==
    \A e \in Edge : CatE[e] \in MessageFlowType <=> (CatN[source[e]] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent} /\ CatN[target[e]] = {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent})
*)

(* TODO WellFormedness for MBE 
- at least 1 input MF (can have more than 1?)
- can have 0 output SF (must have at least 1?)
- attachedTo is defined
- cancelActivity is defined
*)

LOCAL AllConditions == /\ C1_StartNoIncomingEdge
                       /\ C2_EndNoOutgoingEdge
                       /\ C3_SubProcessUniqueStart
                       /\ C4_NoProcessInSubProcess
                       /\ C5_ProcessNode
                       /\ C6_NoLoopingEdge
                       /\ C7_NotIsolation
                       /\ C8_DefaultSeqFlow
                       /\ C9_SendTask
                       /\ C10_ReceiveTask
                       /\ C11_MessageFlowDifferentProcesses
                       /\ C12_EXORTwoOutgoingEdges
                       /\ C13_EXOR_NoConditional
                       /\ C14_EXOR_NextElements

----------------------------------------------------------------

WellFormedness == AllConditions

================================================================
