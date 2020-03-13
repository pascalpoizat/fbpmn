/*
Two processes:
NSE -> ST -> TSE
MSE -> AT -> TSE

CorrectTermination with 10 states
*/


open PWSSyntax
open PWSProp

one sig hello extends MessageKind {}
one sig m extends Message {} {
    from = proc1
    to = proc2
    content = hello
}

one sig st1 extends SendTask {}
one sig se1 extends NoneStartEvent {}
one sig ee1 extends NoneEndEvent {}
one sig mse2 extends MessageStartEvent {}
one sig at2 extends AbstractTask {}
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
    source = mse2
    target = at2
}
one sig f4 extends NormalSequentialFlow {} {
    source = at2
    target = ee2
}
one sig mf extends MessageFlow {} {
    source = st1
    target = mse2
    message = m
}

one sig proc1 extends Process {} {
    contains = se1 + st1 + ee1
}

one sig proc2 extends Process {} {
    contains = mse2 + at2 + ee2
}

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 10 State
check {CorrectTermination} for 0 but 10 State

run {Safe} for 0 but 11 State
