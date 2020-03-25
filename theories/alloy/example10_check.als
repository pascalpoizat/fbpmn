open example10 as m
open PWSProp
open PWSSemantics
open PWSWellformed

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 8 State expect 0
check {CorrectTermination} for 0 but 8 State expect 0

run {Safe} for 0 but 5 Int, 16 State expect 1

/* All end event nodes are reachable. */
run { some s: State | s.nodemarks[ee1a] = 1  } for 0 but 5 State expect 1
run { some s: State | s.nodemarks[ee1b] = 1 } for 0 but 7 State expect 1

check WellFormed for 1 expect 0
