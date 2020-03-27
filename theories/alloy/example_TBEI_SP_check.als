open example_TBEI_SP as m
open PWSProp
open PWSSemantics
open PWSWellformed

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 15 State expect 0
check {CorrectTermination} for 0 but 15 State expect 0

/* Both end events are reachable. */
run { some s: State | s.nodemarks[ee1a] = 1  } for 0 but 9 State expect 1
run { some s: State | s.nodemarks[ee1b] = 1 } for 0 but 11 State expect 1
// but not both simultaneously
run { no s : State | s.nodemarks[ee1a] = 1 && s.nodemarks[ee1b] = 1 } for 0 but 6 Int, 20 State expect 1

check WellFormed for 1 expect 0
