open example6 as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 10 State

check {SimpleTermination} for 0 but 10 State
check {CorrectTermination} for 0 but 10 State
check {EmptyNetTermination} for 0 but 30 State

run {Safe} for 0 but 6 Int, 20 State

check WellFormed
