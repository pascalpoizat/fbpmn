open example1 as m
open PWSSemantics
open PWSProp

check {Safe} for 0 but 10 State

check {SimpleTermination} for 0 but 5 State
check {CorrectTermination} for 0 but 5 State

run {Safe} for 0 but 10 State


