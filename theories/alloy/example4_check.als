open example4 as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 10 State

check {SimpleTermination} for 0 but 9 State
check {CorrectTermination} for 0 but 9 State

run {Safe} for 0 but 11 State

check WellFormed for 1
