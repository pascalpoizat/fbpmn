/*
A process:
NSE -> TICE -> NEE
TICE has either a date or duration constraint.
*/
module example_TICE

open PWSSyntax

one sig se extends NoneStartEvent {}

//one sig titime extends Date {} { date = 4 }
one sig titime extends Duration {} { duration = 4 }
one sig ti extends TimerIntermediateEvent {} {
    mode = titime
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

