/*
Un process avec :
NSE -> PAR -> {AT1,AT2} -> PAR -> TSE
*/


open PWSSyntax
open PWSProp

one sig at1 extends AbstractTask {}
one sig at2 extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}
one sig p1 extends Parallel {}
one sig p2 extends Parallel {}

one sig f1 extends SequentialFlow {} {
    source = se
    target = p1
}
one sig f2 extends SequentialFlow {} {
    source = p1
    target = at1
}
one sig f3 extends SequentialFlow {} {
    source = p1
    target = at2
}
one sig f4 extends SequentialFlow {} {
    source = at1
    target = p2
}
one sig f5 extends SequentialFlow {} {
    source = at2
    target = p2
}
one sig f6 extends SequentialFlow {} {
    source = p2
    target = ee
}
one sig proc extends Process {} {
    contains = se + p1 + at1 + at2 + p2 + ee
}

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 20 State
check {CorrectTermination} for 0 but 5 State

run {Safe} for 0 but 10 State
