/*
Two processes:
NSE -> ST -> NEE
NSE -> RT -> NEE

CorrectTermination with 9 states
*/
module example4

open PWSSyntax
open PWSProp

one sig hello extends Message {}

one sig st1 extends SendTask {}
one sig rt2 extends ReceiveTask {}
one sig se1 extends NoneStartEvent {}
one sig se2 extends NoneStartEvent {}
one sig ee1 extends NoneEndEvent {}
one sig ee2 extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se1
    target = st1
}
one sig f2 extends NormalSequentialFlow {} {
    source = st1
    target = ee1
}
one sig f3 extends NormalSequentialFlow {} {
    source = se2
    target = rt2
}
one sig f4 extends NormalSequentialFlow {} {
    source = rt2
    target = ee2
}
one sig mf extends MessageFlow {} {
    source = st1
    target = rt2
    message = hello
}

one sig proc1 extends Process {} {
    contains = se1 + st1 + ee1
}

one sig proc2 extends Process {} {
    contains = se2 + rt2 + ee2
}
