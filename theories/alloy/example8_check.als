open example8 as m
open PWSSemantics
open PWSProp

check {Safe} for 0 but 7 Int, 10 State

check {SimpleTermination} for 0 but 7 Int, 5 State
check {CorrectTermination} for 0 but 5 State

run {Safe} for 0 but 1 State

run {} for 0 but 7 Int, 10 State


