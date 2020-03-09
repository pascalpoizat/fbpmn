/*
Un process avec :
NSE -> AT -> TSE
*/


open PWSSyntax
open PWSProp

one sig t1 extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}

one sig f1 extends SequentialFlow {} {
    source = se
    target = t1
}
one sig f2 extends SequentialFlow {} {
    source = t1
    target = ee
}

one sig p1 extends Process {} {
    contains = se + t1 + ee
}

check {Safe} for 0 but 10 State

// how can it be true for 2 state?
check {SimpleTermination} for 0 but 2 State
check {CorrectTermination} for 0 but 3 State

run {Safe} for 0 but 2 State
