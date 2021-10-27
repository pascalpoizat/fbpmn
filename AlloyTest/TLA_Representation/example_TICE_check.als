open example_TICE as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 7 Int, 10 State expect 0

/* CorrectTermination with 9 State (to give enough time for the globalclock/localclock to reach 4) */
check {SimpleTermination} for 0 but 9 State expect 0
check {CorrectTermination} for 0 but 9 State expect 0

run {} for 0 but 8 State expect 1

check WellFormed for 1 expect 0


