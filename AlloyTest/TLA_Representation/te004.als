module example_TBENI_SP

open PWSSyntax
open PWSSemantics
open PWSProp
open PWSWellformed
one sig hello extends Message {}

one sig se1 extends NoneStartEvent {}
one sig at1 extends AbstractTask {}
one sig tbe1time extends Duration {} {
    duration = 4
}
one sig tbe1 extends TimerBoundaryEvent {} {
    attachedTo = at1
    interrupting = False
    mode = tbe1time
}
one sig ee1a extends NoneEndEvent {}
one sig ee1b extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se1
    target = at1
}
one sig f2 extends NormalSequentialFlow {} {
    source = at1
    target = ee1a
}
one sig f3 extends NormalSequentialFlow {} {
    source = tbe1
    target = ee1b
}

one sig proc1 extends Process {} {
    contains = se1 + at1 + tbe1 + ee1a + ee1b
}

check {Safe} for 0 but 10 State expect 0
//check {SimpleTermination} for 0 but 15 State expect 0
check {CorrectTermination} for 0 but 15 State expect 0

//run {} for 0 but 5 Int, 16 State expect 1

/* All end event nodes are reachable. */
run { some s: State | s.nodemarks[ee1a] = 1  } for 0 but 7 State expect 1
run { some s: State | s.nodemarks[ee1b] = 1 } for 0 but 9 State expect 1
/* and no both simultaneously */
run { no s : State | s.nodemarks[ee1a] = 1 && s.nodemarks[ee1b] = 1 } for 0 but 14 State expect 1

//check WellFormed for 1 expect 0
