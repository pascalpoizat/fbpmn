open example1 as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 5 State expect 0
check {CorrectTermination} for 0 but 5 State expect 0

run {Safe} for 0 but 3 State expect 1

check WellFormed for 1 expect 0

