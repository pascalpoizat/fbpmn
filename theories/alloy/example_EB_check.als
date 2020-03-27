open example_EB as m
open PWSSemantics
open PWSProp
open PWSWellformed

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

run {Safe} for 0 but 6 Int, 20 State expect 1

check WellFormed for 1 expect 0
