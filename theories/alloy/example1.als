/*
A process:
NSE -> AT -> NEE
*/


open PWSSyntax
open PWSProp

one sig at extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se
    target = at
}
one sig f2 extends NormalSequentialFlow {} {
    source = at
    target = ee
}

one sig p1 extends Process {} {
    contains = se + at + ee
}

check {Safe} for 0 but 10 State

check {SimpleTermination} for 0 but 5 State
check {CorrectTermination} for 0 but 5 State

run {Safe} for 0 but 10 State


