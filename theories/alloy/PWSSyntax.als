module PWSSyntax

/**************** Nodes ****************/
abstract sig Node {}

abstract sig InternalProcess extends Node {
  contains: set Node
}

abstract sig Process extends InternalProcess {}

/** Activities **/
abstract sig Activity extends Node {}
abstract sig AbstractTask extends Activity {}
abstract sig SendTask extends Activity {}
abstract sig ReceiveTask extends Activity {}
abstract sig SubProcess extends InternalProcess {}

/** Gateways **/
abstract sig Gateway extends Node {}
abstract sig ExclusiveOr extends Gateway {}
abstract sig Parallel extends Gateway {}
// to be completed

/**** Events ****/
abstract sig Event extends Node {}

/** Start Events **/
abstract sig StartEvent extends Event {}
abstract sig NoneStartEvent extends Event {}
// to be completed

/** End Events */
abstract sig EndEvent extends Event {}
abstract sig NoneEndEvent extends EndEvent {}
// to be completed

// to be completed IntermediateEvent, BoundaryEvent

/**************** Edges ****************/

abstract sig Edge {
    source: one Node,
    target: one Node
}
abstract sig SequentialFlow extends Edge {}
abstract sig NormalSequentialFlow extends SequentialFlow {}
abstract sig DefaultSequentialFlow extends SequentialFlow {}
abstract sig ConditionalSequentialFlow extends SequentialFlow {}

// abstract MessageFlow extends Edge {
//     msg: Message
// }
