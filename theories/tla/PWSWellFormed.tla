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
    \A n \in Node : CatN[n] = SubProcess => 
        Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType }) = 1

\* not used, and not necessarily true (for tests only)
C3b_SubProcessUniqueEnd ==
    \A n \in Node : CatN[n] = SubProcess =>
        Cardinality(ContainRel[n] \intersect { nn \in Node : CatN[nn] \in EndEventType }) = 1

C4_NoProcessInSubProcess ==
    \A n \in Node : CatN[n] = SubProcess => \A nn \in ContainRel[n] : CatN[nn] # Process

C5_ProcessNode ==
    \A n \in Node : CatN[n] = Process =>
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in StartEventType } # {}
       /\ ContainRel[n] \intersect { nn \in Node : CatN[nn] \in EndEventType } # {}

C6_NoLoopingEdge ==
    \A e \in Edge : source[e] # target[e]

C7_NoNodeIsolation ==
    \A n \in Node : CatN[n] # Process => incoming(n) # {} \/ outgoing(n) # {}

C8_DefaultSeqFlow == \* A gateway that has a conditional edge must have a default edge.
    \A n \in Node : CatN[n] \in GatewayType /\ outtype({ConditionalSeqFlow},n) # {} => Cardinality(outtype({DefaultSeqFlow},n)) = 1

C9_NoIncomingMessageFlow ==
    \A n \in Node : CatN[n] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent} => intype(MessageFlowType,n) = {}

C10_NoOutgoingMessageFlow ==
    \A n \in Node : CatN[n] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent} => outtype(MessageFlowType,n) = {}

C11_MessageFlowDifferentProcesses ==
    \A e \in Edge : CatE[e] \in MessageFlowType => ProcessOf(source[e]) # ProcessOf(target[e])

C12_EBTwoOutgoingEdges ==
    \A n \in Node : CatN[n] = EventBased => Cardinality(outtype(SeqFlowType, n)) >= 2

C13_ParEb_NoConditional ==
    \A n \in Node : CatN[n] \in {Parallel,EventBased} => outtype({ConditionalSeqFlow}, n) = {}

C14_EXOR_NextElements ==
    \A n \in Node : CatN[n] = EventBased =>
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] \in { ReceiveTask, TimerIntermediateEvent }
       \/ \A e \in outtype(SeqFlowType, n) : CatN[target[e]] \in { CatchMessageIntermediateEvent, TimerIntermediateEvent }

C15_OrXor_OutgoingEdges ==
    \A n \in Node : CatN[n] \in {ExclusiveOr,InclusiveOr} =>
       \/ \A e \in outtype(SeqFlowType, n) : CatE[e] \in { ConditionalSeqFlow, DefaultSeqFlow }
       \/ \A e \in outtype(SeqFlowType, n) : CatE[e] \in { NormalSeqFlow }

C16_MessageFlowEdge ==
    \A e \in Edge : CatE[e] \in MessageFlowType =>
       /\ CatN[source[e]] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent}
       /\ CatN[target[e]] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent,MessageBoundaryEvent}

C17_ReceiveIncomingEdge ==
    \A n \in Node : CatN[n] \in {ReceiveTask,MessageStartEvent,CatchMessageIntermediateEvent,MessageBoundaryEvent} => Cardinality(intype(MessageFlowType, n)) >= 1

C18_SendOutgoingEdge ==
    \A n \in Node : CatN[n] \in {SendTask,MessageEndEvent,ThrowMessageIntermediateEvent} => Cardinality(outtype(MessageFlowType, n)) >= 1

----------------------------------------------------------------

\* ASSUME are only checked for the top-level modules, not for imported (extends or instance) modules.

LOCAL AllConditions == /\ C1_StartNoIncomingEdge
                       /\ C2_EndNoOutgoingEdge
                       /\ C3_SubProcessUniqueStart
                       /\ C4_NoProcessInSubProcess
                       /\ C5_ProcessNode
                       /\ C6_NoLoopingEdge
                       /\ C7_NoNodeIsolation
                       /\ C8_DefaultSeqFlow
                       /\ C9_NoIncomingMessageFlow
                       /\ C10_NoOutgoingMessageFlow
                       /\ C11_MessageFlowDifferentProcesses
                       /\ C12_EBTwoOutgoingEdges
                       /\ C13_ParEb_NoConditional
                       /\ C14_EXOR_NextElements
                       /\ C15_OrXor_OutgoingEdges
                       /\ C16_MessageFlowEdge
                       /\ C17_ReceiveIncomingEdge
                       /\ C18_SendOutgoingEdge

----------------------------------------------------------------

WellFormedness == AllConditions

================================================================
