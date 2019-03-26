---------------- MODULE PWSTypes ----------------

(* nodes *)
AbstractTask == "AbstractTask"
SendTask == "SendTask"
ReceiveTask == "ReceiveTask"
Process == "Process"
SubProcess == "SubProcess"
ExclusiveOr == "ExclusiveOr"
InclusiveOr == "InclusiveOr"
Parallel == "Parallel"
EventBasedGateway == "EventBased"
NoneStartEvent == "NoneStartEvent"
MessageStartEvent == "MessageStartEvent"
NoneEndEvent == "NoneEndEvent"
TerminateEndEvent == "TerminateEndEvent"
MessageEndEvent == "MessageEndEvent"
ThrowMessageIntermediateEvent == "ThrowMessageIntermediateEvent"
CatchMessageIntermediateEvent == "CatchMessageIntermediateEvent"
MessageBoundaryEvent == "MessageBoundaryEvent"
(* edges *)
NormalSeqFlow == "NormalSeqFlow"
ConditionalSeqFlow == "ConditionalSeqFlow"
DefaultSeqFlow == "DefaultSeqFlow"
MsgFlow == "MsgFlow"

TaskType == { AbstractTask, SendTask, ReceiveTask }
ActivityType == TaskType \union { SubProcess }
GatewayType == { ExclusiveOr, InclusiveOr, Parallel, EventBasedGateway }
StartEventType == { NoneStartEvent, MessageStartEvent }
EndEventType == { NoneEndEvent, TerminateEndEvent, MessageEndEvent }
IntermediateEventType == { ThrowMessageIntermediateEvent, CatchMessageIntermediateEvent }
BoundaryEventType == { MessageBoundaryEvent }
EventType == StartEventType \union EndEventType \union IntermediateEventType \union BoundaryEventType
NodeType == { Process } \union ActivityType \union GatewayType \union EventType

SeqFlowType == { NormalSeqFlow, ConditionalSeqFlow, DefaultSeqFlow }
MsgFlowType == { MsgFlow }
EdgeType == SeqFlowType \union  MsgFlowType

================================================================
