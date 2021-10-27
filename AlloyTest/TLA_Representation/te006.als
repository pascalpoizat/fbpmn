/*
Two processes:
NSE -> ST -> NEE
NSE -> EB -> RT -> NEE
        | -> TICE -> NEE
*/
module example_EB

open PWSSyntax
open PWSSemantics
open PWSProp
open PWSWellformed

one sig hello extends Message {}

one sig se1 extends NoneStartEvent {}
one sig st1 extends SendTask {}
one sig ee1 extends NoneEndEvent {}

one sig se2 extends NoneStartEvent {}
one sig eb2 extends EventBased {}
one sig rt2a extends ReceiveTask {}
one sig ee2a extends NoneEndEvent {}
one sig ee2b extends NoneEndEvent {}
//one sig xor extends  ExclusiveOr {}

one sig tice2bduration extends Duration {} { duration = 4 }
one sig tice2b extends TimerIntermediateEvent {} {
    mode = tice2bduration
}


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
    target = eb2
}
one sig f4 extends NormalSequentialFlow {} {
    source = eb2
    target = rt2a
}
one sig f5 extends NormalSequentialFlow {} {
    source = rt2a
    target = ee2a
}
one sig f6 extends NormalSequentialFlow {} {
    source = eb2
    target = tice2b
}
one sig f7 extends NormalSequentialFlow {} {
    source = tice2b
    target = ee2b
}
//one sig f8 extends NormalSequentialFlow {} {
   // source = xor
    //target = ee2a
//}
one sig mf extends MessageFlow {} {
    source = st1
    target = rt2a
    message = hello
}

one sig proc1 extends Process {} {
    contains = se1 + st1 + ee1
}

one sig proc2 extends Process {} {
    contains = se2 + eb2 + rt2a + ee2a + tice2b + ee2b
}


check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 14 State expect 0
check {CorrectTermination} for 0 but 14 State expect 0
// EmptyNetTermination is invalid by taking the TICE branch.
check {EmptyNetTermination} for 0 but 14 State expect 1

// Both are reachable
run {! EmptyNetTermination} for 0 but 10 State expect 1
run {EmptyNetTermination} for 0 but 10 State expect 1

// Both end events are reachable
run { some s: State | s.nodemarks[ee2a] = 1 } for 0 but 9 State expect 1
run { some s: State | s.nodemarks[ee2b] = 1 } for 0 but 9 State expect 1

run {} for 0 but 6 Int, 20 State expect 1

check WellFormed for 1 expect 0
