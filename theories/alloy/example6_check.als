open example6 as m
open PWSSemantics
open PWSProp
open PWSWellformed

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 10 State expect 0
check {CorrectTermination} for 0 but 10 State expect 0

// should be consistent but is not, see in example6 expect 0
run {! EmptyNetTermination} for 0 but 20 State expect 1

run {Safe} for 0 but 6 Int, 20 State expect 0

check WellFormed for 1 expect 0
