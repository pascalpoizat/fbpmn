---------------- MODULE PWSTypes ----------------

(* nodes *)
AbstractTask == "AbstractTask"
SendTask == "SendTask"
ReceiveTask == "ReceiveTask"
Process == "Process"
SubProcess == "SubProcess"
ExclusiveOr == "ExclusiveOr" \* a.k.a. XOR
InclusiveOr == "InclusiveOr" \* a.k.a. OR
Parallel == "Parallel"       \* a.k.a AND
EventBased == "EventBased"   \* a.k.a. EXOR
NoneStartEvent == "NoneStartEvent"
MessageStartEvent == "MessageStartEvent"
NoneEndEvent == "NoneEndEvent"
TerminateEndEvent == "TerminateEndEvent"
MessageEndEvent == "MessageEndEvent"
ThrowMessageIntermediateEvent == "ThrowMessageIntermediateEvent"
CatchMessageIntermediateEvent == "CatchMessageIntermediateEvent"
(* edges *)
NormalSeqFlow == "NormalSeqFlow"
ConditionalSeqFlow == "ConditionalSeqFlow"
DefaultSeqFlow == "DefaultSeqFlow"
MessageFlow == "MessageFlow"

TaskType == { AbstractTask, SendTask, ReceiveTask }
ActivityType == TaskType \union { SubProcess }
GatewayType == { ExclusiveOr, InclusiveOr, Parallel, EventBased }
StartEventType == { NoneStartEvent, MessageStartEvent }
EndEventType == { NoneEndEvent, TerminateEndEvent, MessageEndEvent }
EventType == StartEventType \union EndEventType \union { ThrowMessageIntermediateEvent, CatchMessageIntermediateEvent }
NodeType == { Process } \union ActivityType \union GatewayType \union EventType

SeqFlowType == { NormalSeqFlow, ConditionalSeqFlow, DefaultSeqFlow }
MessageFlowType == { MessageFlow }
EdgeType == SeqFlowType \union MessageFlowType

================================================================
