/*
A process:
NSE -> TICE -> NEE

CorrectTermination with 9 State (to give enough time for the globalclock to reach 4)
*/
module example8

open PWSSyntax
open PWSWellformed

one sig se extends NoneStartEvent {}

one sig tidate extends Date {} { date = 4 }
one sig ti extends TimerIntermediateEvent {} {
    mode = tidate
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

