module PWSSemantics

open util/ordering[State]
open util/integer
open util/boolean

open PWSSyntax
open PWSDefs

one sig State {
    var network : set Message,
}

/* all marks except those for n and e are left unchanged.
 * Doesn't care of network. */
pred deltaN[n : Node, e: Edge] {
    all othernode : Node - n | othernode.markn' = othernode.markn
    all otheredge : Edge - e | otheredge.marke' = otheredge.marke
}

/* All marks except those for n and e are left unchanged.
 * Network is left unchanged */
pred delta[n : Node, e: Edge] {
    deltaN[n, e]
    State.network' = State.network
}

/**************** Activities ****************/

/**** Abstract Task ****/

pred canstartAbstractTask[n : AbstractTask] {
    some e: n.intype[SequentialFlow] | e.marke > 0
}

pred startAbstractTask[n: AbstractTask] {
    one e : n.intype[SequentialFlow] {
        e.marke >= 1
        e.marke' = e.marke.dec
        n.markn' = n.markn.inc
        delta[n, e]
    }
}

pred cancompleteAbstractTask[n : Node] {
    n in AbstractTask
    n.markn >= 1
}

pred completeAbstractTask[n : AbstractTask] {
    n.markn >= 1
    n.markn' = n.markn.dec
    all e : n.outtype[SequentialFlow] | e.marke' = e.marke.inc
    delta[n, n.outtype[SequentialFlow]]
}

/**** Send Task ****/

pred canstartSendTask[n : Node] {
    some e : n.intype[SequentialFlow] | e.marke >= 1
}

pred startSendTask[n : SendTask] {
    one e : n.intype[SequentialFlow] {
        e.marke >= 1
        e.marke' = e.marke.dec
        n.markn' = n.markn.inc
        delta[n, e]
    }
}

pred cancompleteSendTask[n : Node] {
    n in SendTask
    n.markn >= 1
    some e : n.outtype[MessageFlow] | cansend[e.message]
}

pred completeSendTask[n : SendTask] {
    n.markn >= 1
    one e : n.outtype[MessageFlow] {
        send[e.message]
        n.markn' = n.markn.dec
        all ee : n.outtype[SequentialFlow] | ee.marke' = ee.marke.inc
        e.marke' = e.marke.inc
        deltaN[n, n.outtype[SequentialFlow] + e]
    }
}

/**** Receive Task ****/

pred canstartReceiveTask[n : Node] {
    some e : n.intype[SequentialFlow] | e.marke >= 1
}

pred startReceiveTask[n : ReceiveTask] {
    one e : n.intype[SequentialFlow] {
        e.marke >= 1
        e.marke' = e.marke.dec
        n.markn' = n.markn.inc
        delta[n, e]
    }
}

pred cancompleteReceiveTask[n : Node] {
    n in ReceiveTask
    n.markn >= 1
    some e : n.intype[MessageFlow] | canreceive[e.message]
}

pred completeReceiveTask[n : ReceiveTask] {
    n.markn >= 1
    one e : n.intype[MessageFlow] {
        receive[e.message]
        n.markn' = n.markn.dec
        all ee : n.outtype[SequentialFlow] | ee.marke' = ee.marke.inc
        e.marke' = e.marke.dec
        deltaN[n, n.outtype[SequentialFlow] + e]
    }
}


/************ Gateways ****************/

pred cancompleteExclusiveOr[n : Node] {
    n in ExclusiveOr
    some ei : n.intype[SequentialFlow] | ei.marke >= 1
}

pred completeExclusiveOr[n: ExclusiveOr] {
    one ei : n.intype[SequentialFlow] {
        ei.marke >= 1
        ei.marke' = ei.marke.dec
        one eo : n.outtype[SequentialFlow] {
            eo.marke' = eo.marke.inc
            delta[none, ei + eo]
        }
    }
}

pred cancompleteParallel[n : Node] {
    n in Parallel
    all ei : n.intype[SequentialFlow] | ei.marke >= 1
}

pred completeParallel[n: Parallel] {
    all ei : n.intype[SequentialFlow] {
        ei.marke >= 1
        ei.marke' = ei.marke.dec
        all eo : n.outtype[SequentialFlow] | eo.marke' = eo.marke.inc
    }
    delta[none, n.intype[SequentialFlow] + n.outtype[SequentialFlow]]
}

pred cancompleteEventBased[n : Node] {
    n in EventBased
    some ei : n.intype[SequentialFlow] | ei.marke >= 1
    some eo : n.outtype[SequentialFlow] {
        { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
          some emsg : eo.target.intype[MessageFlow] | emsg.marke > 0
        }
        or
        { eo.target in TimerIntermediateEvent
          eo.target.canfire
        }
    }
}

pred completeEventBased[n : EventBased] {
    one ei : n.intype[SequentialFlow] {
        ei.marke >= 1
        one eo : n.outtype[SequentialFlow] {
            { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
              some emsg : eo.target.intype[MessageFlow] | emsg.marke > 0
            }
            or
            { eo.target in TimerIntermediateEvent
              eo.target.canfire
            }
            eo.marke' = eo.marke.inc
            ei.marke' = ei.marke.dec
            delta[none, ei + eo]
        }
    }
}

 /************ Events ****************/

/**** Start Events ****/

/* None Start Event */

pred cancompleteNoneStartEvent[n : Node] {
    n in NoneStartEvent
    n.markn >= 1
}

pred completeNoneStartEvent[n: NoneStartEvent] {
    n.markn >= 1
    n.markn' = n.markn.dec
    all e : n.outtype[SequentialFlow] | e.marke' = e.marke.inc
    let p = n.~contains {
        p.markn' = p.markn.inc
        delta[n + p, n.outtype[SequentialFlow]]
    } 
}

/* Message Start Event */

pred canstartMessageStartEvent[n: Node] {
    n in MessageStartEvent
    n.markn = 0
    some e : n.intype[MessageFlow] {
        e.marke >= 1
        canreceive[e.message]
    }
}
pred startMessageStartEvent[n : MessageStartEvent] {
    n.markn = 0
    one e : n.intype[MessageFlow] {
        e.marke >= 1
        receive[e.message]
        e.marke' = e.marke.dec
        n.markn' = n.markn.inc
        deltaN[n, e]
    }
}

pred cancompleteMessageStartEvent[n : Node] {
    n in MessageStartEvent
    n.markn >= 1
    n.processOf.markn = 0
}

pred completeMessageStartEvent[n : MessageStartEvent] {
    n.markn >= 1
    let p = n.processOf {
        p.markn = 0  // no multi-instance
        n.markn' = n.markn.dec
        p.markn' = p.markn.inc
        all e : n.outtype[SequentialFlow] | e.marke' = e.marke.inc
        delta[n + p, n.outtype[SequentialFlow] ]
    }
}

/**** End Events ****/

/* None End Event */

pred canstartNoneEndEvent[n : Node] {
    n in NoneEndEvent
    some e : n.intype[SequentialFlow] | e.marke >= 1
}

pred startNoneEndEvent[n: NoneEndEvent] {
    one e : n.intype[SequentialFlow] {
        e.marke >= 1
        e.marke' = e.marke.dec
        n.markn' = n.markn.inc
        delta[n, e]
    }
}

/* Terminate End Event */

pred canstartTerminateEndEvent[n : Node] {
    n in TerminateEndEvent
    some e : n.intype[SequentialFlow] | e.marke >= 1
}

pred startTerminateEndEvent[n : TerminateEndEvent] {
    one e : n.intype[SequentialFlow] {
        e.marke >= 1
        n.markn' = 1
        let pr = n.~contains,
            edges = { e : Edge | e.source = pr && e.target = pr},
            nodes =  pr.contains - n {
                all e : edges | e.marke' = 0
                all nn : nodes | nn.markn' = 0
                delta[nodes, edges]
        }
    }
}

/* TimerIntermediateEvent */

pred canstartTimerIntermediateEvent[n : Node] {
    n in TimerIntermediateEvent
    some ei : n.intype[SequentialFlow] | ei.marke > 0
    n.canfire
}

pred startTimerIntermediateEvent[n : TimerIntermediateEvent] {
    one ei : n.intype[SequentialFlow] {
        ei.marke' = ei.marke.dec
        all eo : n.outtype[SequentialFlow] | eo.marke' = eo.marke.inc
        delta[none, ei + n.outtype[SequentialFlow]]
    }
}

/************ Time ***************/

pred canfire[n : TimerIntermediateEvent + TimerStartEvent + TimerBoundaryEvent] {
    // conditions handling time
    // Nondeterminism time => true
}


/************ Run ****************/

pred init {
    all e : Edge | e.marke = 0
    let processNSE = { n : NoneStartEvent | n.containInv in Process } {
        all p : processNSE | p.markn = 1
        all n : Node - processNSE | n.markn = 0
    }
    State.network = networkinit
}

pred deadlock {
    no n : Node {
        n.canstartAbstractTask
        or n.cancompleteAbstractTask
        or n.canstartSendTask
        or n.cancompleteSendTask
        or n.canstartReceiveTask
        or n.cancompleteReceiveTask
        or n.cancompleteExclusiveOr
        or n.cancompleteParallel
        or n.cancompleteEventBased
        or n.cancompleteNoneStartEvent
        or n.canstartMessageStartEvent
        or n.cancompleteMessageStartEvent
        or n.canstartNoneEndEvent
        or n.canstartTerminateEndEvent
        or n.canstartTimerIntermediateEvent
    }
}

pred step[n: Node] {
    n in AbstractTask implies { n.startAbstractTask or n.completeAbstractTask }
    else n in SendTask implies { n.startSendTask or n.completeSendTask }
    else n in ReceiveTask implies { n.startReceiveTask or n.completeReceiveTask }
    else n in ExclusiveOr implies n.completeExclusiveOr
    else n in Parallel implies n.completeParallel
    else n in EventBased implies n.completeEventBased
    else n in NoneStartEvent implies n.completeNoneStartEvent
    else n in MessageStartEvent implies { n.startMessageStartEvent or n.completeMessageStartEvent }
    else n in NoneEndEvent implies n.startNoneEndEvent
    else n in TerminateEndEvent implies n.startTerminateEndEvent
    else n in TimerIntermediateEvent implies n.startTimerIntermediateEvent
}

// stutters if no action is possible.
fact traces {
     init
     always {
        deadlock implies delta[none, none]
        else some n : Node - Process | n.step
    }
}

/**************************************************/

/* TODO: replace the set of Message with a bag of Message. */

fun networkinit : set Message { none }

pred cansend[m : Message] {
    // always true
}

pred send[m : Message] {
    State.network' = State.network + m
}

pred canreceive[m : Message] {
        m in State.network
}

pred receive[m : Message] {
    m in State.network
    State.network' = State.network - m
}
