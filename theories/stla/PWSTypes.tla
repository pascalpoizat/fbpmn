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
EventBased == "EventBased"   \* a.k.a. EB
NoneStartEvent == "NoneStartEvent"
MessageStartEvent == "MessageStartEvent"
NoneEndEvent == "NoneEndEvent"
TerminateEndEvent == "TerminateEndEvent"
MessageEndEvent == "MessageEndEvent"
ThrowMessageIntermediateEvent == "ThrowMessageIntermediateEvent"
CatchMessageIntermediateEvent == "CatchMessageIntermediateEvent"
MessageBoundaryEvent == "MessageBoundaryEvent"
TimerStartEvent == "TimerStartEvent"
TimerIntermediateEvent == "TimerIntermediateEvent"
TimerBoundaryEvent == "TimerBoundaryEvent"
(* edges *)
NormalSeqFlow == "NormalSeqFlow"
ConditionalSeqFlow == "ConditionalSeqFlow"
DefaultSeqFlow == "DefaultSeqFlow"
MessageFlow == "MessageFlow"

TaskType == { AbstractTask, SendTask, ReceiveTask }
ActivityType == TaskType \union { SubProcess }
GatewayType == { ExclusiveOr, InclusiveOr, Parallel, EventBased }
StartEventType == { NoneStartEvent, MessageStartEvent, TimerStartEvent }
EndEventType == { NoneEndEvent, TerminateEndEvent, MessageEndEvent }
IntermediateEventType == { ThrowMessageIntermediateEvent, CatchMessageIntermediateEvent, TimerIntermediateEvent }
BoundaryEventType == { MessageBoundaryEvent, TimerBoundaryEvent }
EventType == StartEventType \union EndEventType \union IntermediateEventType \union BoundaryEventType
NodeType == { Process } \union ActivityType \union GatewayType \union EventType

SeqFlowType == { NormalSeqFlow, ConditionalSeqFlow, DefaultSeqFlow }
MessageFlowType == { MessageFlow }
EdgeType == SeqFlowType \union MessageFlowType

(* space BPMN *)
ACT_MOVE == "Move"
ACT_UPDATE == "Update" 
ACT_PASS == "Pass"
Some == "Some"
All == "All"
TypeAction == {ACT_MOVE, ACT_UPDATE, ACT_PASS}
TypeCondition == {Some, All}
(* end space BPMN *)

================================================================
