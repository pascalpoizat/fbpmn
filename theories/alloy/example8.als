/*
A process:
NSE -> TICE -> NEE
*/
module example8

open PWSSyntax
open PWSProp

one sig se extends NoneStartEvent {}

one sig ti extends TimerIntermediateEvent {} {
    mode = Date
    repetition = 0
    duration = 0
    date = 10
}


one sig ee extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se
    target = ti
}
one sig f2 extends NormalSequentialFlow {} {
    source = ti
    target = ee
}

one sig p1 extends Process {} {
    contains = se + ti + ee
}

