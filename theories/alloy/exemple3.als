/*
Un process avec :
NSE -> XOR -> TSE
        |_> AT loop

No SimpleTermination, as it get stuck in the lower branch.
*/


open PWSSyntax
open PWSProp

one sig at extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}
one sig g1 extends ExclusiveOr {}

one sig f1 extends SequentialFlow {} {
    source = se
    target = g1
}
one sig f2 extends SequentialFlow {} {
    source = g1
    target = ee
}
one sig f3 extends SequentialFlow {} {
    source = g1
    target = at
}
one sig f4 extends SequentialFlow {} {
    source = at
    target = at
}

one sig proc extends Process {} {
    contains = se + g1 + at + ee
}

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 20 State
check {CorrectTermination} for 0 but 20 State

run {Safe} for 0 but 11 State
