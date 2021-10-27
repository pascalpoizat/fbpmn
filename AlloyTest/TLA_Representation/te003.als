/*
NSE -> SP[NSE->AT->NEE](TBE -> NEE) -> NEE
       TBE is interrupting
*/
module example_TBEI_SP

open PWSSyntax
open PWSSemantics
open PWSProp
open PWSWellformed

one sig se1 extends NoneStartEvent {}
one sig sp1 extends SubProcess {} {
    contains = se3 + at3 + ee3
}
one sig tbe1time extends Date {} {
    date = 4
}
one sig tb1 extends TimerBoundaryEvent {} {
    attachedTo = sp1
    interrupting = True
    mode = tbe1time
}
one sig se3 extends NoneStartEvent {}
one sig at3 extends AbstractTask {}
one sig ee3 extends NoneEndEvent {}
one sig ee1a extends NoneEndEvent {}
one sig ee1b extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se1
    target = sp1
}
one sig f2 extends NormalSequentialFlow {} {
    source = se3
    target = at3
}
one sig f3 extends NormalSequentialFlow {} {
    source = at3
    target = ee3
}
one sig f4 extends NormalSequentialFlow {} {
    source = sp1
    target = ee1a
}
one sig f5 extends NormalSequentialFlow {} {
    source = tb1
    target = ee1b
}

one sig proc1 extends Process {} {
    contains = se1 + sp1 + tb1 + ee1a + ee1b
}

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 15 State expect 0
check {CorrectTermination} for 0 but 15 State expect 0

/* Both end events are reachable. */
run { some s: State | s.nodemarks[ee1a] = 1  } for 0 but 9 State expect 1
run { some s: State | s.nodemarks[ee1b] = 1 } for 0 but 11 State expect 1
// but not both simultaneously
run { no s : State | s.nodemarks[ee1a] = 1 && s.nodemarks[ee1b] = 1 } for 0 but 6 Int, 20 State expect 1

//check WellFormed for 1 expect 0

