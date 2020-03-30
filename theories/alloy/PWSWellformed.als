module PWSWellformed

open PWSDefs
open PWSSyntax

/* Well-formed conditions */

pred StartNoIncomingEdge {
    all n : StartEvent | n.intype[SequentialFlow] = none
}

pred EndNoOutgoingEdge {
    all n : EndEvent | n.outtype[SequentialFlow] = none
}

pred SubProcessUniqueStart {
    all p : SubProcess | one n : StartEvent | n in p.contains
}

pred NoProcessInSubProcess {
    all p : SubProcess | no pp : Process | pp in p.contains
}

pred ProcessNode {
    all p : Process {
        some n : StartEvent | n in p.contains
        some n : EndEvent | n in p.contains
    }
}

pred NoLoopingEdge {
    no e : Edge | e.source = e.target
}

pred NoNodeIsolation {
    all n : Node - Process | some e : Edge | e.source = n or e.target = n
}

pred DefaultSequentialFlow { // A gateway that has a conditional edge must have a default edge.
    all n : Gateway | (n.outtype[ConditionalSequentialFlow] != none) implies one n.outtype[DefaultSequentialFlow]
}

pred NoIncomingMessageFlow {
    all n : SendTask + MessageEndEvent + ThrowMessageIntermediateEvent | n.intype[MessageFlow] = none
}

pred NoOutgoingMessageFlow {
    all n : ReceiveTask + MessageStartEvent + CatchMessageIntermediateEvent | n.outtype[MessageFlow] = none
}

pred MessageFlowDifferentProcesses {
    no m : MessageFlow | (m.source.processOf = m.target.processOf)
}

pred EBTwoOutgoingEdges {
    all n : EventBased | some disj e1, e2 : Edge | e1 in n.outtype[SequentialFlow] && e2 in n.outtype[SequentialFlow]
}

pred ParEb_NoConditional {
    all n : Parallel + EventBased | n.outtype[ConditionalSequentialFlow] = none
}

pred EB_NextElements {
    all n : EventBased {
            all e : n.outtype[SequentialFlow] | e.target in ReceiveTask + TimerIntermediateEvent
        or
            all e : n.outtype[SequentialFlow] | e.target in CatchMessageIntermediateEvent + TimerIntermediateEvent
    }
}

pred OrXor_OutgoingEdges {
    all n : ExclusiveOr + InclusiveOr {
            all e : n.outtype[SequentialFlow] | e in ConditionalSequentialFlow + DefaultSequentialFlow
        or
            all e : n.outtype[SequentialFlow] | e in NormalSequentialFlow
    }
}

pred MessageFlowEdge {
    all e : MessageFlow {
        e.source in SendTask + MessageEndEvent + ThrowMessageIntermediateEvent
        e.target in ReceiveTask + MessageStartEvent + CatchMessageIntermediateEvent + MessageBoundaryEvent
    }
}

pred ReceiveIncomingEdge {
    all n : ReceiveTask + MessageStartEvent + CatchMessageIntermediateEvent + MessageBoundaryEvent |
        n.intype[MessageFlow] != none
}

pred SendOutgoingEdge {
    all n : SendTask + MessageEndEvent + ThrowMessageIntermediateEvent |
        n.outtype[MessageFlow] != none
}

assert WellFormed {
    StartNoIncomingEdge
    EndNoOutgoingEdge
    SubProcessUniqueStart
    NoProcessInSubProcess
    ProcessNode
    NoLoopingEdge
    NoNodeIsolation
    DefaultSequentialFlow
    NoIncomingMessageFlow
    NoOutgoingMessageFlow
    MessageFlowDifferentProcesses
    EBTwoOutgoingEdges
    ParEb_NoConditional
    EB_NextElements
    OrXor_OutgoingEdges
    MessageFlowEdge
    ReceiveIncomingEdge
    SendOutgoingEdge
}
