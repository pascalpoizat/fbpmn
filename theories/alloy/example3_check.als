open example3 as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 20 State
check {CorrectTermination} for 0 but 20 State

run {Safe} for 0 but 11 State

check WellFormed
