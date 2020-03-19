/*
Two processes:
NSE -> ST -> NEE
NSE -> EB -> RT -> NEE
        | -> TICE -> NEE
        
CorrectTermination with 10 states
EmptyNetTermination should be invalid (by taking the TICE branch)
 [ but is currently valid - to be debugged ]
*/
module example6

open PWSSyntax
open PWSProp

one sig hello extends Message {}

one sig se1 extends NoneStartEvent {}
one sig st1 extends SendTask {}
one sig ee1 extends NoneEndEvent {}

one sig se2 extends NoneStartEvent {}
one sig eb2 extends EventBased {}
one sig rt2a extends ReceiveTask {}
one sig ee2a extends NoneEndEvent {}
one sig tice2b extends TimerIntermediateEvent {} {
    mode = Date
    date = 4
    duration = 0
    repetition = 0
}
one sig ee2b extends NoneEndEvent {}

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

