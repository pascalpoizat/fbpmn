/*
A process:
NSE -> PAR -> {AT1,AT2} -> PAR -> NEE
*/


open PWSSyntax
open PWSProp

one sig at1 extends AbstractTask {}
one sig at2 extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}
one sig p1 extends Parallel {}
one sig p2 extends Parallel {}

one sig f1 extends NormalSequentialFlow {} {
    source = se
    target = p1
}
one sig f2 extends NormalSequentialFlow {} {
    source = p1
    target = at1
}
one sig f3 extends NormalSequentialFlow {} {
    source = p1
    target = at2
}
one sig f4 extends NormalSequentialFlow {} {
    source = at1
    target = p2
}
one sig f5 extends NormalSequentialFlow {} {
    source = at2
    target = p2
}
one sig f6 extends NormalSequentialFlow {} {
    source = p2
    target = ee
}
one sig proc extends Process {} {
    contains = se + p1 + at1 + at2 + p2 + ee
}

check {Safe} for 0 but 20 State

check {SimpleTermination} for 0 but 20 State
check {CorrectTermination} for 0 but 20 State

run {Safe} for 0 but 15 State

run {} for 0 but 11 State
