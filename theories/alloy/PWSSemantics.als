module PWSSemantics

open util/ordering[State]
open util/integer
open util/boolean

open PWSSyntax
open PWSDefs

sig State {
    nodemarks : Node -> one Int,
    edgemarks : Edge -> one Int,
    network : set Message,
}

/* all marks except those for n and e are left unchanged.
 * Doesn't care of network. */
pred deltaN[s, s': State, n : Node, e: Edge] {
    all othernode : Node - n | s'.nodemarks[othernode] = s.nodemarks[othernode]
    all otheredge : Edge - e | s'.edgemarks[otheredge] = s.edgemarks[otheredge]
}

/* All marks except those for n and e are left unchanged.
 * Network is left unchanged */
pred delta[s, s': State, n : Node, e: Edge] {
    deltaN[s, s', n, e ]
    s'.network = s.network
}

/**************** Activities ****************/

/**** Abstract Task ****/

pred State.canstartAbstractTask[n : AbstractTask] {
    some e: n.intype[SequentialFlow] | this.edgemarks[e] > 0
}

pred startAbstractTask[s, s': State, n: AbstractTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] >= 1
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
    }
}

pred State.cancompleteAbstractTask[n : Node] {
    n in AbstractTask
    this.nodemarks[n] >= 1
}

pred completeAbstractTask[s, s' : State, n : AbstractTask] {
    s.nodemarks[n] >= 1
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    delta[s, s', n, n.outtype[SequentialFlow]]
}

/**** Send Task ****/

pred State.canstartSendTask[n : Node] {
    some e : n.intype[SequentialFlow] | this.edgemarks[e] >= 1
}

pred startSendTask[s, s' : State, n : SendTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] >= 1
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
    }
}

pred State.cancompleteSendTask[n : Node] {
    n in SendTask
    this.nodemarks[n] >= 1
    some e : n.outtype[MessageFlow] | cansend[this, e.message]
}

pred completeSendTask[s, s' : State, n : SendTask] {
    s.nodemarks[n] >= 1
    one e : n.outtype[MessageFlow] {
        send[s, s', e.message]
        s'.nodemarks[n] = s.nodemarks[n].dec
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        s'.edgemarks[e] = s.edgemarks[e].inc
        deltaN[s, s', n, n.outtype[SequentialFlow] + e]
    }
}

/**** Receive Task ****/

pred State.canstartReceiveTask[n : Node] {
    some e : n.intype[SequentialFlow] | this.edgemarks[e] >= 1
}

pred startReceiveTask[s, s' : State, n : ReceiveTask] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] >= 1
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
    }
}

pred State.cancompleteReceiveTask[n : Node] {
    n in ReceiveTask
    this.nodemarks[n] >= 1
    some e : n.intype[MessageFlow] | canreceive[this, e.message]
}

pred completeReceiveTask[s, s' : State, n : ReceiveTask] {
    s.nodemarks[n] >= 1
    one e : n.intype[MessageFlow] {
        receive[s, s', e.message]
        s'.nodemarks[n] = s.nodemarks[n].dec
        all ee : n.outtype[SequentialFlow] | s'.edgemarks[ee] = s.edgemarks[ee].inc
        s'.edgemarks[e] = s.edgemarks[e].dec
        deltaN[s, s', n, n.outtype[SequentialFlow] + e]
    }
}


/************ Gateways ****************/

pred State.cancompleteExclusiveOr[n : Node] {
    n in ExclusiveOr
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] >= 1
}

pred completeExclusiveOr[s, s' : State, n: ExclusiveOr] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        one eo : n.outtype[SequentialFlow] {
            s'.edgemarks[eo] = s.edgemarks[eo].inc
            delta[s, s', none, ei + eo]
        }
    }
}

pred State.cancompleteParallel[n : Node] {
    n in Parallel
    all ei : n.intype[SequentialFlow] | this.edgemarks[ei] >= 1
}

pred completeParallel[s, s' : State, n: Parallel] {
    all ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
    }
    delta[s, s', none, n.intype[SequentialFlow] + n.outtype[SequentialFlow]]
}

pred State.cancompleteEventBased[n : Node] {
    n in EventBased
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] >= 1
    some eo : n.outtype[SequentialFlow] {
        { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
          some emsg : eo.target.intype[MessageFlow] | this.edgemarks[emsg] > 0
        }
        or
        { eo.target in TimerIntermediateEvent
          this.canfire[eo.target]
        }
    }
}

pred completeEventBased[s, s' : State, n : EventBased] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] >= 1
        one eo : n.outtype[SequentialFlow] {
            { eo.target in (ReceiveTask + CatchMessageIntermediateEvent)
              some emsg : eo.target.intype[MessageFlow] | s.edgemarks[emsg] > 0
            }
            or
            { eo.target in TimerIntermediateEvent
              s.canfire[eo.target]
            }
            s'.edgemarks[eo] = s.edgemarks[eo].inc
            s'.edgemarks[ei] = s.edgemarks[ei].dec
            delta[s, s', none, ei + eo]
        }
    }
}

 /************ Events ****************/

/**** Start Events ****/

/* None Start Event */

pred State.cancompleteNoneStartEvent[n : Node] {
    n in NoneStartEvent
    this.nodemarks[n] >= 1
}

pred completeNoneStartEvent[s, s' : State, n: NoneStartEvent] {
    s.nodemarks[n] >= 1
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    let p = n.~contains {
        s'.nodemarks[p] = s.nodemarks[p].inc
        delta[s, s', n + p, n.outtype[SequentialFlow]]
    } 
}

/* Message Start Event */

pred State.canstartMessageStartEvent[n: Node] {
    n in MessageStartEvent
    this.nodemarks[n] = 0
    some e : n.intype[MessageFlow] {
        this.edgemarks[e] >= 1
        canreceive[this, e.message]
    }
}
pred startMessageStartEvent[s, s' : State, n : MessageStartEvent] {
    s.nodemarks[n] = 0
    one e : n.intype[MessageFlow] {
        s.edgemarks[e] >= 1
        receive[s, s', e.message]
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        deltaN[s, s', n, e]
    }
}

pred State.cancompleteMessageStartEvent[n : Node] {
    n in MessageStartEvent
    this.nodemarks[n] >= 1
    this.nodemarks[n.processOf] = 0
}

pred completeMessageStartEvent[s, s': State, n : MessageStartEvent] {
    s.nodemarks[n] >= 1
    let p = n.processOf {
        s.nodemarks[p] = 0  // no multi-instance
        s'.nodemarks[n] = s.nodemarks[n].dec
        s'.nodemarks[p] = s.nodemarks[p].inc
        all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
        delta[s, s', n + p, n.outtype[SequentialFlow] ]
    }
}

/**** End Events ****/

/* None End Event */

pred State.canstartNoneEndEvent[n : Node] {
    n in NoneEndEvent
    some e : n.intype[SequentialFlow] | this.edgemarks[e] >= 1
}

pred startNoneEndEvent[s, s' : State, n: NoneEndEvent] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] >= 1
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
    }
}

/* Terminate End Event */

pred State.canstartTerminateEndEvent[n : Node] {
    n in TerminateEndEvent
    some e : n.intype[SequentialFlow] | this.edgemarks[e] >= 1
}

pred startTerminateEndEvent[s, s' : State, n : TerminateEndEvent] {
    one e : n.intype[SequentialFlow] {
        s.edgemarks[e] >= 1
        s'.nodemarks[n] = 1
        let pr = n.~contains,
            edges = { e : Edge | e.source = pr && e.target = pr},
            nodes =  pr.contains - n {
                all e : edges | s'.edgemarks[e] = 0
                all nn : nodes | s'.nodemarks[nn] = 0
                delta[s, s', nodes, edges]
        }
    }
}

/* TimerIntermediateEvent */

pred State.canstartTimerIntermediateEvent[n : Node] {
    n in TimerIntermediateEvent
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] > 0
    this.canfire[n]
}

pred startTimerIntermediateEvent[s, s' : State, n : TimerIntermediateEvent] {
    one ei : n.intype[SequentialFlow] {
        s.edgemarks[ei] > 0
        s.canfire[n]
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
        delta[s, s', none, ei + n.outtype[SequentialFlow]]
    }
}

/************ Time ***************/

pred State.canfire[n : TimerIntermediateEvent + TimerStartEvent + TimerBoundaryEvent] {
    // conditions handling time
    // Nondeterminism time => true
}


/************ Run ****************/

pred initialState {
    first.edgemarks = (Edge -> 0)
    let processNSE = { n : NoneStartEvent | n.containInv in Process } {
        first.nodemarks = (Node -> 0) ++ (processNSE -> 1)
    }
    first.network = networkinit
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
        or this.canstartMessageStartEvent[n]
        or this.cancompleteMessageStartEvent[n]
        or this.canstartNoneEndEvent[n]
        or this.canstartTerminateEndEvent[n]
        or this.canstartTimerIntermediateEvent[n]
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
    else n in MessageStartEvent implies { startMessageStartEvent[s,s',n] or completeMessageStartEvent[s,s',n] }
    else n in NoneEndEvent implies startNoneEndEvent[s, s', n]
    else n in TerminateEndEvent implies startTerminateEndEvent[s, s', n]
    else n in TimerIntermediateEvent implies startTimerIntermediateEvent[s, s', n]
}

fact init { initialState }

// stutters if no action is possible.
fact traces {
	all s: State - last {
        s.deadlock implies delta[s, s.next, none, none]
        else some n : Node - Process | step[s, s.next, n]
    }
}

/**************************************************/

/* TODO: replace the set of Message with a bag of Message. */

fun networkinit : set Message { none }

pred cansend[s : State, m : Message] {
    // always true
}

pred send[s, s' : State, m : Message] {
    s'.network = s.network + m
}

pred canreceive[s : State, m : Message] {
        m in s.network
}

pred receive[s, s' : State, m : Message] {
    m in s.network
    s'.network = s.network - m
}
