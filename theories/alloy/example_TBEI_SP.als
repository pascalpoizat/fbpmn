/*
NSE -> SP[NSE->AT->NEE](TBE -> NEE) -> NEE
       TBE is interrupting
*/
module example_TBEI_SP

open PWSSyntax
open PWSSemantics

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

