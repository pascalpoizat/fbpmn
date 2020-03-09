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
    let othernodes = Node - n | s'.nodemarks[othernodes] = s.nodemarks[othernodes]
    let otheredges = Edge - e | s'.edgemarks[otheredges] = s.edgemarks[otheredges]
}

/**************** Activities ****************/

/* useless?
pred State.canstartAbstractTask(n : AbstractTask) {
    some e: n.incoming[SequentialFlow] | this.edgemarks[e] > 0
}
*/

pred startAbstractTask[s, s': State, n: AbstractTask] {
     s'.nodemarks[n] = s.nodemarks[n] + 1
     one e : n.intype[SequentialFlow] | {
         s.edgemarks[e] >= 1
         s'.edgemarks[e] = s.edgemarks[e] - 1
        delta[s, s', none, e]
     }
 }

pred completeAbstractTask[s, s' : State, n : AbstractTask] {
     s.nodemarks[n] >= 1
     s'.nodemarks[n] = s.nodemarks[n] - 1
     all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e] + 1
     delta[s, s', none, n.outtype[SequentialFlow]]
 }

 /************ Gateways ****************/

pred completeExclusiveOr[s, s' : State, n: ExclusiveOr] {
     one ei : n.intype[SequentialFlow] | {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s'.edgemarks[ei] - 1
        one eo : n.outtype[SequentialFlow] | {
            s'.edgemarks[eo] = s.edgemarks[eo] + 1
            delta[s, s', none, ei + eo]
        }
     }
}

pred completeParallel[s, s' : State, n: Parallel] {
     all ei : n.intype[SequentialFlow] | {
        s.edgemarks[ei] >= 1
        s'.edgemarks[ei] = s'.edgemarks[ei] - 1
        all eo : n.outtype[SequentialFlow] | s'.edgemarks[eo] = s.edgemarks[eo] + 1
        delta[s, s', none, n.intype[SequentialFlow] + n.outtype[SequentialFlow]]
     }
}

 /************ Events ****************/

pred completeStartEvent[s, s' : State, n: NoneStartEvent] {
     s.nodemarks[n] >= 1
     s'.nodemarks[n] = s.nodemarks[n] - 1
     all e : n.outtype[SequentialFlow] | s'.edgemarks[e] = s.edgemarks[e] + 1
     some p : Process | {
         n in p.contains
         s'.nodemarks[p] = s.nodemarks[p] + 1
         delta[s, s', n + p, n.outtype[SequentialFlow]]
     } 
 }

pred startEndEvent[s, s' : State, n: NoneEndEvent] {
     one e : n.intype[SequentialFlow] {
         s.edgemarks[e] >= 1
         s'.edgemarks[e] = s.edgemarks[e] - 1
         s'.nodemarks[n] = s.nodemarks[n] + 1
         delta[s, s', n, e]
     }
 }

/************ Run ****************/

pred initialState {
    first.edgemarks = (Edge -> 0)
    first.nodemarks = (Node -> 0) ++ (NoneStartEvent -> 1)
}

pred step[s, s' : State, n: Node] {
      n in AbstractTask implies { startAbstractTask[s,s',n] or completeAbstractTask[s,s',n] }
      else
      n in ExclusiveOr implies completeExclusiveOr[s,s',n]
      else
      n in Parallel implies completeParallel[s,s',n]
      else
      n in NoneStartEvent implies completeStartEvent[s,s',n]
      else
      n in NoneEndEvent implies startEndEvent[s, s', n]
      else
      n in Process implies s' = s
      else
      s' = s
  }

fact init { initialState }

fact traces {
	all s: State - last | some n : Node | step[s, s.next, n]
}