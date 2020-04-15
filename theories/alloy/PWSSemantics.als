module PWSSemantics

open util/ordering[State]
open util/integer
open util/boolean

open PWSSyntax
open PWSDefs

sig State {
    nodemarks : Node -> one Int,
    edgemarks : Edge -> one Int,
    network : set (Message -> Process -> Process),
    globalclock : one Int,
    localclock : (TimerStartEvent + TimerIntermediateEvent + TimerBoundaryEvent) -> one Int,
}

/* Time is left unchanged except for node n. */
pred deltaT[s, s' : State, n : TimerIntermediateEvent + TimerStartEvent + TimerBoundaryEvent] {
    all nn : Node - n | s'.localclock[nn] = s.localclock[nn]
    s'.globalclock = s.globalclock
}

/* all marks except those for n and e are left unchanged.
 * Doesn't care about network or time. */
pred deltaN[s, s': State, n : Node, e: Edge] {
    all othernode : Node - n | s'.nodemarks[othernode] = s.nodemarks[othernode]
    all otheredge : Edge - e | s'.edgemarks[otheredge] = s.edgemarks[otheredge]
}

/* All marks except those for n and e are left unchanged.
 * Network is left unchanged.
 * doesn't care about time. */
pred delta[s, s': State, n : Node, e: Edge] {
    deltaN[s, s', n, e ]
    s'.network = s.network
}

/*********************************************/

// pred State.subprocessMayComplete[n : SubProcess] { this.cancompleteSubProcess[n] }

/**************** Activities ****************/

/**** Abstract Task ****/

pred State.canstartAbstractTask[n : Node] {
    n in AbstractTask
    some e: n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startAbstractTask[s, s': State, n: AbstractTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
        let te = { t : n.~attachedTo & TimerBoundaryEvent | t.mode in Duration - CycleStart } {
            all t : te | s'.localclock[t] = 1
            deltaT[s, s', te]
        }
    }
}

pred State.cancompleteAbstractTask[n : Node] {
    n in AbstractTask
    this.nodemarks[n] > 0
}

pred completeAbstractTask[s, s' : State, n : AbstractTask] {
    s.nodemarks[n] > 0
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    delta[s, s', n, n.outtype[SequentialFlow]]
    let te = { t : n.~attachedTo & TimerBoundaryEvent | t.mode in Duration } {
        all t : te | s'.localclock[t] = 0
        deltaT[s, s', te]
    }
}

/**** Send Task ****/

pred State.canstartSendTask[n : Node] {
    n in SendTask
    some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startSendTask[s, s' : State, n : SendTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
        deltaT[s, s', none]
    }
}

pred State.cancompleteSendTask[n : Node] {
    n in SendTask
    this.nodemarks[n] > 0
    some e : n.outtype[MessageFlow] | this.cansend[e.message, e.source.processOf, e.target.processOf]
}

pred completeSendTask[s, s' : State, n : SendTask] {
    s.nodemarks[n] > 0
    one e : n.outtype[MessageFlow] {
        send[s, s', e.message, e.source.processOf, e.target.processOf]
        s'.nodemarks[n] = s.nodemarks[n].dec
        s'.edgemarks[e] = s.edgemarks[e].inc
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        deltaN[s, s', n, n.outtype[SequentialFlow] + e]
        deltaT[s, s', none]
    }
}

/**** Receive Task ****/

pred State.canstartReceiveTask[n : Node] {
    n in ReceiveTask
    some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startReceiveTask[s, s' : State, n : ReceiveTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
        deltaT[s, s', none]
    }
}

pred State.cancompleteReceiveTask[n : Node] {
    n in ReceiveTask
    this.nodemarks[n] > 0
    some e : n.intype[MessageFlow] { this.edgemarks[e] > 0 && this.canreceive[e.message, e.source.processOf, e.target.processOf] }
}

pred completeReceiveTask[s, s' : State, n : ReceiveTask] {
    s.nodemarks[n] > 0
    one e : n.intype[MessageFlow] {
        s.edgemarks[e] > 0
        receive[s, s', e.message, e.source.processOf, e.target.processOf]
        s'.nodemarks[n] = s.nodemarks[n].dec
        s'.edgemarks[e] = s.edgemarks[e].dec
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        deltaN[s, s', n, n.outtype[SequentialFlow] + e]
        deltaT[s, s', none]
    }
}

/**** SubProcess ****/

pred State.canstartSubProcess[n : Node] {
    n in SubProcess
    this.nodemarks[n] = 0 // no reenter
    some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startSubProcess[s, s' : State, n : SubProcess] {
    s.nodemarks[n] = 0 // no reenter
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.edgemarks[e] = s.edgemarks[e].dec
        let se = (n.contains & StartEvent) {
            all nn : se | s'.nodemarks[nn] = s.nodemarks[nn].inc
            s'.nodemarks[n] = s.nodemarks[n].inc
            delta[s, s', n + se, e]
            let te = { t : n.~attachedTo & TimerBoundaryEvent | t.mode in Duration - CycleStart } {
                all t : te | s'.localclock[t] = 1
                deltaT[s, s', te]
            }
        }
    }
}

pred State.cancompleteSubProcess[n : Node] {
    n in SubProcess
    this.nodemarks[n] > 0
    all e : Edge { (e.source in n.contains && e.target in n.contains) implies this.edgemarks[e] = 0 }
    some nee : n.contains & EndEvent | this.nodemarks[nee] > 0
    all nn : n.contains | this.nodemarks[nn] = 0 or nn in EndEvent
}

pred completeSubProcess[s, s' : State, n : SubProcess] {
    s.cancompleteSubProcess[n]
    s'.nodemarks[n] = 0
    all nee : n.contains & EndEvent | s'.nodemarks[nee] = 0
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    delta[s, s', n + (n.contains & EndEvent), n.outtype[SequentialFlow]]
    let te = { t : n.~attachedTo & TimerBoundaryEvent | t.mode in Duration } {
        all t : te | s'.localclock[t] = 0
        deltaT[s, s', te]
    }
}


/************ Gateways ****************/

pred State.cancompleteExclusiveOr[n : Node] {
    n in ExclusiveOr
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0
}

pred completeExclusiveOr[s, s' : State, n: ExclusiveOr] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] > 0
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        one eo : n.outtype[SequentialFlow] {
            s'.edgemarks[eo] = s.edgemarks[eo].inc
            delta[s, s', none, ei + eo]
            deltaT[s, s', none]
        }
    }
}

pred State.cancompleteParallel[n : Node] {
    n in Parallel
    all ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0
}

pred completeParallel[s, s' : State, n: Parallel] {
    all ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] > 0
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
    }
    delta[s, s', none, n.intype[SequentialFlow] + n.outtype[SequentialFlow]]
    deltaT[s, s', none]
}

pred State.cancompleteEventBased[n : Node] {
    n in EventBased
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0
    some eo : n.outtype[SequentialFlow] {
        { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
          some emsg : eo.target.intype[MessageFlow] | this.edgemarks[emsg] > 0
        }
        or
        { eo.target in TimerIntermediateEvent
          this.canfire[eo.target <: TimerIntermediateEvent]
        }
    }
}

pred completeEventBased[s, s' : State, n : EventBased] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] > 0
        one eo : n.outtype[SequentialFlow] {
            { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
              some emsg : eo.target.intype[MessageFlow] | s.edgemarks[emsg] > 0
            }
            or
            { eo.target in TimerIntermediateEvent
              s.canfire[eo.target <: TimerIntermediateEvent]
            }
            s'.edgemarks[eo] = s.edgemarks[eo].inc
            s'.edgemarks[ei] = s.edgemarks[ei].dec
            delta[s, s', none, ei + eo]
            deltaT[s, s', none]
        }
    }
}

 /************ Events ****************/

/**** Start Events ****/

/* None Start Event */

pred State.cancompleteNoneStartEvent[n : Node] {
    n in NoneStartEvent
    this.nodemarks[n] > 0
}

pred completeNoneStartEvent[s, s' : State, n: NoneStartEvent] {
    s.nodemarks[n] > 0
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    let p = n.~contains {
        {
            p in Process
            s'.nodemarks[p] = s.nodemarks[p].inc
            delta[s, s', n + p, n.outtype[SequentialFlow]]
        } or {
            p in SubProcess
            delta[s, s', n, n.outtype[SequentialFlow]]
        }
        deltaT[s, s', none]
    }
}

/* Timer Start Event */

pred State.cancompleteTimerStartEvent[n : Node] {
    n in TimerStartEvent
    this.nodemarks[n] > 0
    this.canfire[n <: TimerStartEvent]
}

pred completeTimerStartEvent[s, s' : State, n: TimerStartEvent] {
    s.nodemarks[n] > 0
    s.canfire[n]
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    let p = n.~contains {
        s'.nodemarks[p] = s.nodemarks[p].inc
        delta[s, s', n + p, n.outtype[SequentialFlow]]
        deltaT[s, s', none] // localclock is unused
    }
}

/* Message Start Event */

pred State.canstartMessageStartEvent[n: Node] {
    n in MessageStartEvent
    this.nodemarks[n] = 0
    some e : n.intype[MessageFlow] {
        this.edgemarks[e] > 0
        this.canreceive[e.message, e.source.processOf, e.target.processOf]
    }
}
pred startMessageStartEvent[s, s' : State, n : MessageStartEvent] {
    s.nodemarks[n] = 0
    one e : n.intype[MessageFlow] {
        s.edgemarks[e] > 0
        receive[s, s', e.message, e.source.processOf, e.target.processOf]
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        deltaN[s, s', n, e]
        deltaT[s, s', none]
    }
}

pred State.cancompleteMessageStartEvent[n : Node] {
    n in MessageStartEvent
    this.nodemarks[n] > 0
    this.nodemarks[n.processOf] = 0
}

pred completeMessageStartEvent[s, s': State, n : MessageStartEvent] {
    s.nodemarks[n] > 0
    let p = n.processOf {
        s.nodemarks[p] = 0  // no multi-instance
        s'.nodemarks[n] = s.nodemarks[n].dec
        s'.nodemarks[p] = s.nodemarks[p].inc
        all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
        delta[s, s', n + p, n.outtype[SequentialFlow] ]
        deltaT[s, s', none]
    }
}

/**** End Events ****/

/* None End Event */

pred State.canstartNoneEndEvent[n : Node] {
    n in NoneEndEvent
    some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startNoneEndEvent[s, s' : State, n: NoneEndEvent] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
        deltaT[s, s', none]
    }
}

/* Terminate End Event */

pred State.canstartTerminateEndEvent[n : Node] {
    n in TerminateEndEvent
    some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startTerminateEndEvent[s, s' : State, n : TerminateEndEvent] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] > 0
        s'.nodemarks[n] = 1
        let pr = n.~contains,
            edges = { e : Edge | e.source = pr && e.target = pr},
            nodes =  pr.contains - n {
                all e : edges | s'.edgemarks[e] = 0
                all nn : nodes | s'.nodemarks[nn] = 0
                delta[s, s', nodes, edges]
                deltaT[s, s', none]
        }
    }
}

/* Message End Event */

pred State.canstartMessageEndEvent[n : Node] {
    n in MessageEndEvent
    some e1 : n.intype[SequentialFlow], e2 : n.outtype[MessageFlow] {
        this.edgemarks[e1] > 0
        this.cansend[e2.message, e2.source.processOf, e2.target.processOf]
    }
}

pred startMessageEndEvent[s, s' : State, n : MessageEndEvent] {
    one e1 : n.intype[SequentialFlow], e2 : n.outtype[MessageFlow] {
        s.edgemarks[e1] > 0
        send[s, s', e2.message, e2.source.processOf, e2.target.processOf]
        s'.edgemarks[e1] = s.edgemarks[e1].dec
        s'.edgemarks[e2] = s.edgemarks[e2].inc
        s'.nodemarks[n] = s.nodemarks[n].inc
        deltaN[s, s', n, e1 + e2]
        deltaT[s, s', none]
    }
}

/**** Intermediate Events ****/

/* Throw Message Intermediate Event TMIE */

pred State.canstartThrowMessageIntermediateEvent[n : Node] {
    n in ThrowMessageIntermediateEvent
    some e1 : n.intype[SequentialFlow] | this.edgemarks[e1] > 0
    some e2 : n.outtype[MessageFlow] | this.cansend[e2.message, e2.source.processOf, e2.target.processOf]
}

pred startThrowMessageIntermediateEvent[s, s' : State, n : ThrowMessageIntermediateEvent] {
    one e1 : n.intype[SequentialFlow], e2 : n.outtype[MessageFlow] {
        s.edgemarks[e1] > 0
        send[s, s', e2.message, e2.source.processOf, e2.target.processOf]
        s'.edgemarks[e1] = s.edgemarks[e1].dec
        s'.edgemarks[e2] = s.edgemarks[e2].inc
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        deltaN[s, s', none, n.outtype[SequentialFlow] + e1 + e2]
        deltaT[s, s', none]
    }
}

/* Catch Message Intermediate Event CMIE */

pred State.canstartCatchMessageIntermediateEvent[n : Node] {
    n in CatchMessageIntermediateEvent
    some e1 : n.intype[SequentialFlow] | this.edgemarks[e1] > 0
    some e2 : n.intype[MessageFlow] { this.edgemarks[e2] > 0 && this.canreceive[e2.message, e2.source.processOf, e2.target.processOf] }
}

pred startCatchMessageIntermediateEvent[s, s' : State, n : CatchMessageIntermediateEvent] {
    one e1 : n.intype[SequentialFlow], e2 : n.intype[MessageFlow] {
        s.edgemarks[e1] > 0
        s.edgemarks[e2] > 0
        receive[s, s', e2.message, e2.source.processOf, e2.target.processOf]
        s'.edgemarks[e1] = s.edgemarks[e1].dec
        s'.edgemarks[e2] = s.edgemarks[e2].dec
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        deltaN[s, s', none, n.outtype[SequentialFlow] + e1 + e2]
        deltaT[s, s', none]
    }
}

/* Timer Intermediate Event TICE */

pred State.canstartTimerIntermediateEvent[n : Node] {
    n in TimerIntermediateEvent
    (n <: TimerIntermediateEvent).mode in Duration
    this.localclock[n] = 0
    (some ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0)
    or (some e : n.intype[SequentialFlow] {
               e.source in EventBased
               some e' : e.source.intype[SequentialFlow] | this.edgemarks[e'] > 0
          })
}

pred startTimerIntermediateEvent[s, s' : State, n : TimerIntermediateEvent] {
    s.canstartTimerIntermediateEvent[n]
    s'.localclock[n] = 1
    delta[s, s', none, none]
    deltaT[s, s', n]
}

pred State.cancompleteTimerIntermediateEvent[n : Node] {
    n in TimerIntermediateEvent
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0
    this.canfire[n <: TimerIntermediateEvent]
}

pred completeTimerIntermediateEvent[s, s' : State, n : TimerIntermediateEvent] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] > 0
        s.canfire[n]
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
        delta[s, s', none, ei + n.outtype[SequentialFlow]]
        n.mode in Duration implies { s'.localclock[n] = 0 && deltaT[s, s', n] }
        else deltaT[s, s', none]
    }
}

/**** Boundary Events *****/

/* Message Boundary Event */

pred State.canstartMessageBoundaryEvent[n : Node] {
    n in MessageBoundaryEvent
    this.nodemarks[n.attachedTo] > 0
    some ei : n.intype[MessageFlow] {
        this.edgemarks[ei] > 0
        canreceive[this, ei.message, ei.source.processOf, ei.target.processOf]    
    }
    (n.interrupting.isTrue && n.attachedTo in SubProcess) => not this.cancompleteSubProcess[n.attachedTo]
}

pred startMessageBoundaryEvent_Basic[s, s' : State, n : MessageBoundaryEvent, interrupted: lone Task] {
    s.nodemarks[n.attachedTo] > 0
    one ei : n.intype[MessageFlow] {
        s.edgemarks[ei] > 0
        receive[s, s', ei.message, ei.source.processOf, ei.target.processOf]
        s'.edgemarks[ei] = s.edgemarks[ei].dec            
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
        (interrupted = none) or (s'.nodemarks[interrupted] = 0)
        deltaN[s, s', interrupted, ei + n.outtype[SequentialFlow]]
        deltaT[s, s', none]
    }
}

pred startMessageBoundaryEvent_InterruptingProcess[s, s' : State, n : MessageBoundaryEvent] {
    let act = n.attachedTo <: SubProcess {
        s.nodemarks[act] > 0
        not s.cancompleteSubProcess[act]
        one ei : n.intype[MessageFlow] {
            s.edgemarks[ei] > 0
            receive[s, s', ei.message, ei.source.processOf, ei.target.processOf]
            all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
            s'.edgemarks[ei] = s.edgemarks[ei].dec
            let includednodes = act.^contains {  // interrupt the subprocess
                s'.nodemarks[act] = 0
                all inc : includednodes | s'.nodemarks[inc] = 0
                let inedges = { e : Edge | e.source in includednodes && e.target in includednodes } {
                    all ee : inedges | s'.edgemarks[ee] = 0
                    deltaN[s, s', act + includednodes, ei + n.outtype[SequentialFlow] + inedges]
                    deltaT[s, s', none]
                }
            }
        }
    }
}

pred startMessageBoundaryEvent[s, s' : State, n : MessageBoundaryEvent ] {
    n.attachedTo in Task && n.interrupting.isTrue implies startMessageBoundaryEvent_Basic[s, s', n, n.attachedTo]
    else n.attachedTo in Task && n.interrupting.isFalse implies startMessageBoundaryEvent_Basic[s, s', n, none]
    else n.attachedTo in SubProcess && n.interrupting.isTrue implies startMessageBoundaryEvent_InterruptingProcess[s, s', n]
    else n.attachedTo in SubProcess && n.interrupting.isFalse implies startMessageBoundaryEvent_Basic[s, s', n, none]
}

/* Timer Boundary Event */

/* special case of TBENIcycle with start date */
pred State.canstartTimerBoundaryEvent[n : Node] {
    n in TimerBoundaryEvent
    this.nodemarks[n.attachedTo] > 0
    let nn = n <: TimerBoundaryEvent {
        nn.mode in CycleStart
        // nn.interrupting.isFalse should be a fact
        this.globalclock >= (nn.mode <: CycleStart).startdate
        this.localclock[nn] = 0
        // s.record[nn] = (nn.mode <: CycleStart).repetition
    }
}

/* special case of TBENIcycle with start date */
pred startTimerBoundaryEvent[s, s' : State, n : TimerBoundaryEvent ] {
    s.canfire[n]
    s'.localclock[n] = 1
    // s'.record[n] = s.record[n].dec
    delta[s, s', none, none]
    deltaT[s, s', n]
}

/* TODO: repetition */

pred State.cancompleteTimerBoundaryEvent[n : Node] {
    n in TimerBoundaryEvent
    this.nodemarks[n.attachedTo] > 0
    this.canfire[n <: TimerBoundaryEvent]
    (n.interrupting.isTrue && n.attachedTo in SubProcess) => not this.cancompleteSubProcess[n.attachedTo]
}

pred completeTimerBoundaryEvent_Basic[s, s' : State, n : TimerBoundaryEvent, interrupted: lone Task] {
    s.nodemarks[n.attachedTo] > 0
    s.canfire[n]
    all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
    (interrupted = none) or (s'.nodemarks[interrupted] = 0)
    s'.localclock[n] = 0  // actually only if Duration
    deltaN[s, s', interrupted, n.outtype[SequentialFlow]]
    deltaT[s, s', n]
}

pred completeTimerBoundaryEvent_InterruptingProcess[s, s' : State, n : TimerBoundaryEvent] {
    let act = n.attachedTo <: SubProcess {
        s.nodemarks[act] > 0
        not s.cancompleteSubProcess[act]
        s.canfire[n]
        s'.localclock[n] = 0  // actually only if Duration
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
        let includednodes = act.^contains {  // interrupt the subprocess
            s'.nodemarks[act] = 0
            all inc : includednodes | s'.nodemarks[inc] = 0
            let inedges = { e : Edge | e.source in includednodes && e.target in includednodes } {
                all ee : inedges | s'.edgemarks[ee] = 0
                deltaN[s, s', act + includednodes, n.outtype[SequentialFlow] + inedges]
                deltaT[s, s', none]
            }
        }
    }
}

pred completeTimerBoundaryEvent[s, s' : State, n : TimerBoundaryEvent ] {
    n.attachedTo in Task && n.interrupting.isTrue implies completeTimerBoundaryEvent_Basic[s, s', n, n.attachedTo]
    else n.attachedTo in Task && n.interrupting.isFalse implies completeTimerBoundaryEvent_Basic[s, s', n, none]
    else n.attachedTo in SubProcess && n.interrupting.isTrue implies completeTimerBoundaryEvent_InterruptingProcess[s, s', n]
    else n.attachedTo in SubProcess && n.interrupting.isFalse implies completeTimerBoundaryEvent_Basic[s, s', n, none]
}


/************ Time ***************/

pred State.canfire[n : TimerIntermediateEvent] {
    { n.mode in Date && this.globalclock = (n.mode <: Date).date }
    or
    { n.mode in Duration && this.localclock[n] >= (n.mode <: Duration).duration }
}

pred State.canfire[n : TimerStartEvent] {
    n.mode in Date && this.globalclock >= n.mode.date
}

pred State.canfire[n : TimerBoundaryEvent] {
    { n.mode in Date && this.globalclock = (n.mode <: Date).date }
    or
    { n.mode in Duration && this.localclock[n] = (n.mode <: Duration).duration }
}



/************ Run ****************/

pred initialState {
    first.edgemarks = (Edge -> 0)
    let processNSE = { n : NoneStartEvent + TimerStartEvent | n.containInv in Process } {
        first.nodemarks = (Node -> 0) ++ (processNSE -> 1)
    }
    first.network = networkinit
    first.globalclock = 0
    first.localclock = (TimerStartEvent + TimerIntermediateEvent + TimerBoundaryEvent) -> 0
}

// Is a timer ticking? I.E. waiting for time to advance and not ready to fire.
pred State.someTimerIsActive {
    // easy case: a local clock is counting
    { some n : TimerStartEvent | this.localclock[n] > 0 && not this.canfire[n] }
    or { some n : TimerIntermediateEvent | this.localclock[n] > 0 && not this.canfire[n] }
    or { some n : TimerBoundaryEvent | this.localclock[n] > 0 && not this.canfire[n] }
    or // a TSE is waiting to fire
    { some n : TimerStartEvent | n.mode in Date && this.nodemarks[n] = 1 && not this.canfire[n] }
    or // a TICE is waiting to fire
    { some n : TimerIntermediateEvent | n.mode in Date && not this.canfire[n] && some e : n.intype[SequentialFlow] | this.edgemarks[e] > 0 }
    or // a TICE follows an EB which is waiting to fire
    { some n : TimerIntermediateEvent | n.mode in Date && not this.canfire[n] && some e : n.intype[SequentialFlow] | { e.source in EventBased && some ee : e.source.intype[SequentialFlow] | this.edgemarks[ee] > 0 } }
    or // a TBE attached to an active node
    { some n : TimerBoundaryEvent | n.mode in Date && not this.canfire[n] && this.nodemarks[n.attachedTo] > 0 }
}

pred State.deadlock {
    no n : Node {
        this.canstartAbstractTask[n]
        or this.cancompleteAbstractTask[n]
        or this.canstartSendTask[n]
        or this.cancompleteSendTask[n]
        or this.canstartReceiveTask[n]
        or this.cancompleteReceiveTask[n]
        or this.cancompleteExclusiveOr[n]
        or this.cancompleteParallel[n]
        or this.cancompleteEventBased[n]
        or this.cancompleteNoneStartEvent[n]
        or this.cancompleteTimerStartEvent[n]
        or this.canstartMessageStartEvent[n]
        or this.cancompleteMessageStartEvent[n]
        or this.canstartNoneEndEvent[n]
        or this.canstartTerminateEndEvent[n]
        or this.canstartMessageEndEvent[n]
        or this.canstartThrowMessageIntermediateEvent[n]
        or this.canstartCatchMessageIntermediateEvent[n]
        or this.canstartTimerIntermediateEvent[n]
        or this.cancompleteTimerIntermediateEvent[n]
        or this.canstartSubProcess[n]
        or this.cancompleteSubProcess[n]
        or this.canstartMessageBoundaryEvent[n]
        or this.canstartTimerBoundaryEvent[n]
        or this.cancompleteTimerBoundaryEvent[n]
    }
}

pred step[s, s' : State, n: Node] {
    n in AbstractTask implies { startAbstractTask[s,s',n] or completeAbstractTask[s,s',n] }
    else n in SendTask implies { startSendTask[s,s',n] or completeSendTask[s,s',n] }
    else n in ReceiveTask implies { startReceiveTask[s,s',n] or completeReceiveTask[s,s',n] }
    else n in ExclusiveOr implies completeExclusiveOr[s,s',n]
    else n in Parallel implies completeParallel[s,s',n]
    else n in EventBased implies completeEventBased[s,s',n]
    else n in NoneStartEvent implies completeNoneStartEvent[s,s',n]
    else n in TimerStartEvent implies completeTimerStartEvent[s,s',n]
    else n in MessageStartEvent implies { startMessageStartEvent[s,s',n] or completeMessageStartEvent[s,s',n] }
    else n in NoneEndEvent implies startNoneEndEvent[s, s', n]
    else n in TerminateEndEvent implies startTerminateEndEvent[s, s', n]
    else n in MessageEndEvent implies startMessageEndEvent[s, s', n]
    else n in ThrowMessageIntermediateEvent implies startThrowMessageIntermediateEvent[s, s', n]
    else n in CatchMessageIntermediateEvent implies startCatchMessageIntermediateEvent[s, s', n]
    else n in TimerIntermediateEvent implies { startTimerIntermediateEvent[s, s', n] or completeTimerIntermediateEvent[s, s', n] }
    else n in SubProcess implies { startSubProcess[s, s', n] or completeSubProcess[s, s', n]}
    else n in MessageBoundaryEvent implies startMessageBoundaryEvent[s, s', n]
    else n in TimerBoundaryEvent implies { startTimerIntermediateEvent[s, s', n] or completeTimerBoundaryEvent[s, s', n] }
}

fact init { initialState }

pred advancetime[s, s': State] {
     // see below: time advances only if deadlock.
     // no n : TimerStartEvent + TimerIntermediateEvent + TimerBoundaryEvent | s.canfire[n]
     all n : TimerStartEvent + TimerIntermediateEvent + TimerBoundaryEvent {
         // isn't timerActive iff localclock[n] > 0 ?
         s.localclock[n] > 0 implies s'.localclock[n] = s.localclock[n].inc
         else s'.localclock[n] = s.localclock[n]
     }
     s'.globalclock = s.globalclock.inc
}

/* As we are doing bounded model-checking, we must ensure that enough steps are done.
 * Formally, with infinite executions, weak-fairness is sufficient.
 * With bounded model-checking, if advancetime is always possible, we could just take it and waste any number of steps.
 * Our solution is to advance time only when nothing else is possible.
 * However one must take care of ticking timers: time may also advance if one exists.
 */
fact traces {
    all s: State - last {
        { (s.deadlock or s.someTimerIsActive) && delta[s, s.next, none, none] && advancetime[s, s.next] }
        or
        { some n : Node - Process | step[s, s.next, n] }
    }
}

/**************************************************/

/* Enhancement: replace the set of Message with a bag of Message. */

fun networkinit : set (Message -> Process -> Process) { none -> none -> none  }

pred State.cansend[m : Message, from: Process, to: Process] {
    // always true
}

pred send[s, s' : State, m : Message, from: Process, to: Process] {
    s.cansend[m, from, to]
    s'.network = s.network + (m -> from -> to)
}

pred State.canreceive[m : Message, from: Process, to: Process] {
        (m -> from -> to) in this.network
}

pred receive[s, s' : State, m : Message, from: Process, to: Process] {
    s.canreceive[m, from, to]
    s'.network = s.network - (m -> from -> to)
}

/*************************************************/

/**** Consistency ****/

/* commented out once verified, to avoid overloading Alloy. */

/*
assert { all s: State, n : Node |  s.canstartAbstractTask[n] iff (some s': State | startAbstractTask[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteAbstractTask[n] iff (some s': State | completeAbstractTask[s, s', n]) }
assert { all s: State, n : Node |  s.canstartSendTask[n] iff (some s': State | startSendTask[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteSendTask[n] iff (some s': State | completeSendTask[s, s', n]) }
assert { all s: State, n : Node |  s.canstartReceiveTask[n] iff (some s': State | startReceiveTask[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteReceiveTask[n] iff (some s': State | completeReceiveTask[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteExclusiveOr[n] iff (some s': State | completeExclusiveOr[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteParallel[n] iff (some s': State | completeParallel[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteEventBased[n] iff (some s': State | completeEventBased[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteNoneStartEvent[n] iff (some s': State | completeNoneStartEvent[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteTimerStartEvent[n] iff (some s': State | completeTimerStartEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartMessageStartEvent[n] iff (some s': State | startMessageStartEvent[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteMessageStartEvent[n] iff (some s': State | completeMessageStartEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartNoneEndEvent[n] iff (some s': State | startNoneEndEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartTerminateEndEvent[n] iff (some s': State | startTerminateEndEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartMessageEndEvent[n] iff (some s': State | startMessageEndEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartThrowMessageIntermediateEvent[n] iff (some s': State | startThrowMessageIntermediateEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartCatchMessageIntermediateEvent[n] iff (some s': State | startCatchMessageIntermediateEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartTimerIntermediateEvent[n] iff (some s': State | startTimerIntermediateEvent[s, s', n]) }
assert { all s: State, n : Node |  s.canstartSubProcess[n] iff (some s': State | startSubProcess[s, s', n]) }
assert { all s: State, n : Node |  s.cancompleteSubProcess[n] iff (some s': State | completeSubProcess[s, s', n]) }
assert { all s: State, n : Node |  s.canstartMessageBoundaryEvent[n] iff (some s': State | startMessageBoundaryEvent[s, s', n]) }
*/
