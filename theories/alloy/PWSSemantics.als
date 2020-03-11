module PWSSemantics

open util/ordering[State]
open util/integer
open util/boolean

open PWSSyntax
open PWSDefs

sig State {
    nodemarks : Node -> one Int,
    edgemarks : Edge -> one Int
    // network
}

/* all marks except those for n and e are left unchanged. */
pred delta[s, s': State, n : Node, e: Edge] {
    all othernode : Node - n | s'.nodemarks[othernode] = s.nodemarks[othernode]
    all otheredge : Edge - e | s'.edgemarks[otheredge] = s.edgemarks[otheredge]
}

/**************** Activities ****************/

pred State.canstartAbstractTask(n : AbstractTask) {
    some e: n.intype[SequentialFlow] | this.edgemarks[e] > 0
}


pred startAbstractTask[s, s': State, n: AbstractTask] {
    one e : n.intype[SequentialFlow] | {
        s.edgemarks[e] >= 1
        s'.edgemarks[e] = s.edgemarks[e].dec
        s'.nodemarks[n] = s.nodemarks[n].inc
        delta[s, s', n, e]
    }
}

pred State.cancompleteAbstractTask(n : Node) {
    n in AbstractTask
    this.nodemarks[n] >= 1
}

pred completeAbstractTask[s, s' : State, n : AbstractTask] {
    s.nodemarks[n] >= 1
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | { s'.edgemarks[e] = s.edgemarks[e].inc }
    delta[s, s', n, n.outtype[SequentialFlow]]
}

 /************ Gateways ****************/

pred State.cancompleteExclusiveOr(n : Node) {
    n in ExclusiveOr
    some ei : n.intype[SequentialFlow] | this.edgemarks[ei] >= 1
}

pred completeExclusiveOr[s, s' : State, n: ExclusiveOr] {
    one ei : n.intype[SequentialFlow] | {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        one eo : n.outtype[SequentialFlow] | {
            s'.edgemarks[eo] = s.edgemarks[eo].inc
            delta[s, s', none, ei + eo]
        }
    }
}

pred State.cancompleteParallel(n : Node) {
    n in Parallel
    all ei : n.intype[SequentialFlow] | this.edgemarks[ei] >= 1
}

pred completeParallel[s, s' : State, n: Parallel] {
    all ei : n.intype[SequentialFlow] | {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s.edgemarks[ei].dec
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo].inc
    }
    delta[s, s', none, n.intype[SequentialFlow] + n.outtype[SequentialFlow]]
}

 /************ Events ****************/

pred State.cancompleteNoneStartEvent(n : Node) {
    n in NoneStartEvent
    this.nodemarks[n] >= 1
}

pred completeNoneStartEvent[s, s' : State, n: NoneStartEvent] {
    s.nodemarks[n] >= 1
    s'.nodemarks[n] = s.nodemarks[n].dec
    all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e].inc
    let p = n.~contains | {
        s'.nodemarks[p] = s.nodemarks[p].inc
        delta[s, s', n + p, n.outtype[SequentialFlow]]
    } 
}

pred State.canstartNoneEndEvent(n : Node) {
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

/************ Run ****************/

pred initialState {
    first.edgemarks = (Edge -> 0)
    first.nodemarks = (Node -> 0) ++ (NoneStartEvent -> 1)
}

pred State.deadlock {
    no n : Node | {
        this.canstartAbstractTask[n]
        or this.cancompleteAbstractTask[n]
        or this.cancompleteExclusiveOr[n]
        or this.cancompleteParallel[n]
        or this.cancompleteNoneStartEvent[n]
        or this.canstartNoneEndEvent[n]
    }
}

pred step[s, s' : State, n: Node] {
    n in AbstractTask implies { startAbstractTask[s,s',n] or completeAbstractTask[s,s',n] }
    else
    n in ExclusiveOr implies completeExclusiveOr[s,s',n]
    else
    n in Parallel implies completeParallel[s,s',n]
    else
    n in NoneStartEvent implies completeNoneStartEvent[s,s',n]
    else
    n in NoneEndEvent implies startNoneEndEvent[s, s', n]
}

fact init { initialState }

fact traces {
    // il faut bégayer si on ne peut rien faire d'autre. Comment ?
	all s: State - last {
        s.deadlock implies delta[s, s.next, none, none]
        else some n : Node - Process | step[s, s.next, n]
    }
}
