/*
Two processes:
NSE -> SP[NSE->AT->NEE](MBE -> NEE) -> NEE
       MBE is interrupting
NSE -> TMIE -> NEE
*/
module example12

open PWSSyntax
open PWSSemantics

one sig hello extends Message {}

one sig se1 extends NoneStartEvent {}
one sig sp1 extends SubProcess {} {
    contains = se3 + at3 + ee3
}
one sig mb1 extends MessageBoundaryEvent {} {
    attachedTo = sp1
    interrupting = True
}
one sig se3 extends NoneStartEvent {}
one sig at3 extends AbstractTask {}
one sig ee3 extends NoneEndEvent {}
one sig ee1a extends NoneEndEvent {}
one sig ee1b extends NoneEndEvent {}

one sig se2 extends NoneStartEvent {}
one sig tm2 extends ThrowMessageIntermediateEvent {}
one sig ee2 extends NoneEndEvent {}

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
    source = mb1
    target = ee1b
}
one sig f1b extends NormalSequentialFlow {} {
    source = se2
    target = tm2
}
one sig f2b extends NormalSequentialFlow {} {
    source = tm2
    target = ee2
}
one sig mf extends MessageFlow {} {
    source = tm2
    target = mb1
    message = hello
}

one sig proc1 extends Process {} {
    contains = se1 + sp1 + mb1 + ee1a + ee1b
}

one sig proc2 extends Process {} {
    contains = se2 + tm2 + ee2
}
