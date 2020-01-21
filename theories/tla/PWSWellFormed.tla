---------------- MODULE PWSWellFormed ----------------
(* Rules of well-structureness *)

EXTENDS PWSDefs, PWSTypes

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

----------------------------------------------------------------
C1_SubProcessUniqueStart ==
    \A n \in Node : CatN[n] = SubProcess => 
        Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType }) = 1

\* not used (for tests only)
C1b_SubProcessUniqueEnd ==
    \A n \in Node : CatN[n] = SubProcess =>
        Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in EndEventType }) = 1

C2_NoProcessInSubProcess ==
    \A n \in Node : CatN[n] = SubProcess => \A nn \in ContainRel[n] : CatN[nn] # Process

C3_ProcessNode ==
    \A n \in Node : CatN[n] = Process =>
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType } # {}
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in EndEventType } # {}
    \* /\ Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] = Process }) = 1 \* impossible

C4_NoLoopingEdge ==
    \A e \in Edge : source[e] # target[e]

C5_NoNodeIsolation ==
    \A n \in Node : CatN[n] # Process => incoming(n) # {} \/ outgoing(n) # {}

C6_DefaultSeqFlow == \* A gateway that has a conditional edge must have a default edge.
    \A n \in Node : CatN[n] \in GatewayType /\ outtype({ConditionalSeqFlow},n) # {} => Cardinality(outtype({DefaultSeqFlow},n)) = 1

C7_NoIncomingMessageFlow ==
    \A n \in Node : CatN[n] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent} => intype(MessageFlowType,n) = {}

C8_NoOutgoingMessageFlow ==
    \A n \in Node : CatN[n] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent} => outtype(MessageFlowType,n) = {}

C9_MessageFlowDifferentProcesses ==
    \A ni, nj \in Processes, e \in Edge : CatE[e] \in MessageFlowType /\ source[e] \in ContainRel[ni] /\ target[e] \in ContainRel[nj] => ni # nj

C10_EBTwoOutgoingEdges ==
    \A n \in Node : CatN[n] = EventBased => Cardinality(outtype(SeqFlowType, n)) >= 2

C11_ParEb_NoConditional ==
    \A n \in Node : CatN[n] \in {Parallel,EventBased} => outtype({ConditionalSeqFlow}, n) = {}

C12_EXOR_NextElements ==
    \A n \in Node : CatN[n] = EventBased =>
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] \in { ReceiveTask, TimerIntermediateEvent }
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] \in { CatchMessageIntermediateEvent, TimerIntermediateEvent }

C13_OrXor_OutgoingEdges ==
    \A n \in Node : CatN[n] \in {ExclusiveOr,InclusiveOr} =>
       \/ \A e \in outtype(SeqFlowType, n) : CatE[e] \in { ConditionalSeqFlow, DefaultSeqFlow }
       \/ \A e \in outtype(SeqFlowType, n) : CatE[e] \in { NormalSeqFlow }

C14_MessageFlowEdge ==
    \A e \in Edge : CatE[e] \in MessageFlowType =>
       /\ CatN[source[e]] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent}
       /\ CatN[target[e]] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent,MessageBoundaryEvent}

C15_ReceiveIncomingEdge ==
    \A n \in Node : CatN[n] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent,MessageBoundaryEvent} => Cardinality(intype(MessageFlowType, n)) >= 1

C16_SendOutgoingEdge ==
    \A n \in Node : CatN[n] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent} => Cardinality(outtype(MessageFlowType, n)) >= 1

----------------------------------------------------------------

\********* OLD ********

Cx_StartNoIncomingEdge ==
    \A n \in Node : CatN[n] \in StartEventType => intype(SeqFlowType,n) = {}

Cx_EndNoOutgoingEdge ==
    \A n \in Node : CatN[n] \in EndEventType => outtype(SeqFlowType,n) = {}

Cx_SubProcessContainsEnd ==
    \A n \in Node : CatN[n] = SubProcess => 
        /\ \E se \in ContainRel[n] : CatN[se] = NoneStartEvent

\*****************

----------------------------------------------------------------

\* ASSUME are only checked for the top-level modules, not for imported (extends or instance) modules.

LOCAL AllConditions == /\ C1_SubProcessUniqueStart
                       /\ C2_NoProcessInSubProcess
                       /\ C3_ProcessNode
                       /\ C4_NoLoopingEdge
                       /\ C5_NoNodeIsolation
                       /\ C6_DefaultSeqFlow
                       /\ C7_NoIncomingMessageFlow
                       /\ C8_NoOutgoingMessageFlow
                       /\ C9_MessageFlowDifferentProcesses
                       /\ C10_EBTwoOutgoingEdges
                       /\ C11_ParEb_NoConditional
                       /\ C12_EXOR_NextElements
                       /\ C13_OrXor_OutgoingEdges
                       /\ C14_MessageFlowEdge
                       /\ C15_ReceiveIncomingEdge
                       /\ C16_SendOutgoingEdge

----------------------------------------------------------------

WellFormedness == AllConditions

================================================================
