/*
Two processes:
NSE -> AT -> MEE
MSE -> AT -> NEE
*/
module example9

open PWSSyntax

one sig hello extends Message {}

one sig se1 extends NoneStartEvent {}
one sig at1 extends AbstractTask {}
one sig mee1 extends MessageEndEvent {}
one sig mse2 extends MessageStartEvent {}
one sig at2 extends AbstractTask {}
one sig ee2 extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se1
    target = at1
}
one sig f2 extends NormalSequentialFlow {} {
    source = at1
    target = mee1
}
one sig f3 extends NormalSequentialFlow {} {
    source = mse2
    target = at2
}
one sig f4 extends NormalSequentialFlow {} {
    source = at2
    target = ee2
}
one sig mf extends MessageFlow {} {
    source = mee1
    target = mse2
    message = hello
}

one sig proc1 extends Process {} {
    contains = se1 + at1 + mee1
}

one sig proc2 extends Process {} {
    contains = mse2 + at2 + ee2
}
