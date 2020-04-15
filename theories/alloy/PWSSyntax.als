module PWSSyntax

open util/boolean

/**** Message Names ****/
abstract sig Message {}

/**** Time ****/

/* Timer nodes have a constraint that can be a date, a duration, or a
   duration with a repetition factor. In this last case, it can also have a
   starting date xor an ending date.
   TSE can only have a Date, TICE can have Date or Duration, TBE any one.
*/
abstract sig Date {
    date : one Int
}
abstract sig Duration {
    duration : one Int
}
abstract sig CycleDuration extends Duration {
    repetition : one Int,
}
abstract sig CycleStart extends CycleDuration {
    startdate  : one Int
}
abstract sig CycleEnd extends CycleDuration {
    enddate    : one Int
}


/**************** Nodes ****************/

abstract sig Node {}

abstract sig Container extends Node {
  contains: set Node
}
fact ContainerNotReflexive { no p : Container | p in p.^contains }
fact NoFreeNode { all n : Node - Process | one p : Container | n in p.contains }

abstract sig Process extends Container {}

/** Activities **/
abstract sig Task extends Node {}
abstract sig AbstractTask extends Task {}
abstract sig SendTask extends Task {}
abstract sig ReceiveTask extends Task {}
abstract sig SubProcess extends Container {}

/** Gateways **/
abstract sig Gateway extends Node {}
abstract sig ExclusiveOr extends Gateway {}
abstract sig Parallel extends Gateway {}
abstract sig InclusiveOr extends Gateway {}
abstract sig EventBased extends Gateway {}

/**** Events ****/
abstract sig Event extends Node {}

/** Start Events **/
abstract sig StartEvent extends Event {}
abstract sig NoneStartEvent extends StartEvent {}
abstract sig MessageStartEvent extends StartEvent {}
abstract sig TimerStartEvent extends StartEvent {
    mode       : one Date
}

/** End Events */
abstract sig EndEvent extends Event {}
abstract sig NoneEndEvent extends EndEvent {}
abstract sig TerminateEndEvent extends EndEvent {}
abstract sig MessageEndEvent extends EndEvent {}

/** Intermediate Events */
abstract sig IntermediateEvent extends Event {}
abstract sig ThrowMessageIntermediateEvent extends IntermediateEvent {}
abstract sig CatchMessageIntermediateEvent extends IntermediateEvent {}
abstract sig TimerIntermediateEvent extends IntermediateEvent {
    mode       : one (Date + Duration),
}

/** Boundary Events */
abstract sig BoundaryEvent extends Event {
    attachedTo : one (Task + SubProcess),
    interrupting : one Bool
}

abstract sig MessageBoundaryEvent extends BoundaryEvent {}
abstract sig TimerBoundaryEvent extends BoundaryEvent {
    mode       : one (Date + Duration)
}

/**************** Edges ****************/

abstract sig Edge {
    source: one Node,
    target: one Node
}
abstract sig SequentialFlow extends Edge {}
abstract sig NormalSequentialFlow extends SequentialFlow {}
abstract sig DefaultSequentialFlow extends SequentialFlow {}
abstract sig ConditionalSequentialFlow extends SequentialFlow {}

abstract sig MessageFlow extends Edge {
     message: one Message
}

// process of this node
fun Node.processOf : Process {
    this.^(~contains) & Process
}
