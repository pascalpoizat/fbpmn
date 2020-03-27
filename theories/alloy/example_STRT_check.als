open example_STRT as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 9 State expect 0
check {CorrectTermination} for 0 but 9 State expect 0

run {Safe} for 0 but 11 State expect 1

check WellFormed for 1 expect 0