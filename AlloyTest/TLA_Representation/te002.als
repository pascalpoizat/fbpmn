/*
A process:
NSE -> TICE -> NEE
TICE has either a date or duration constraint.
*/
module e002

open PWSSyntax
open PWSSemantics
open PWSProp
open PWSWellformed

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


check {Safe} for 0 but 7 Int, 10 State expect 0
/* CorrectTermination with 9 State (to give enough time for the globalclock/localclock to reach 4) */
check {SimpleTermination} for 0 but 10 State expect 0
check {CorrectTermination} for 0 but 10 State expect 0

run {} for 0 but 8 State expect 1

check WellFormed for 1 expect 0


