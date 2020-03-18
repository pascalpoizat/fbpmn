open example7 as m
open PWSSemantics
open PWSProp

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 7 State
check {CorrectTermination} for 0 but 7 State

run {Safe} for 0 but 12 State
