module PWSSyntax

/**** Message Names ****/
abstract sig MessageKind {}
abstract sig Message {
    from : Process,
    to : Process,
    content : MessageKind
}

/**** Time ****/

abstract sig TimeMode {}
one sig Date extends TimeMode {}
one sig Duration extends TimeMode {}
one sig Cycle extends TimeMode {} 


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
    ctime : Int,
    mode  : TimeMode
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
    ctime : Int,
    mode  : TimeMode
}

/** Boundary Events */
abstract sig BoundaryEvent extends Event {}
abstract sig MessageBoundaryEvent extends BoundaryEvent {}
abstract sig TimerBoundaryEvent extends BoundaryEvent {
    ctime : Int,
    mode  : TimeMode
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
     message: Message
}
{ message.from = source.processOf && message.to = target.processOf }

// process of this node
fun Node.processOf : Process {
    this.^(~contains) & Process
}
