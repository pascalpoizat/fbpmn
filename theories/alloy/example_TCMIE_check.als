open example_TCMIE as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 15 State expect 0

check {SimpleTermination} for 0 but 7 State expect 0
check {CorrectTermination} for 0 but 7 State expect 0

run {Safe} for 0 but 12 State expect 1

check WellFormed for 1 expect 0
