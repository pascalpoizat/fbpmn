open example3 as m
open PWSSemantics
open PWSProp
open PWSWellformed

/*
With XOR and NEE/TEE: No SimpleTermination, as it can get stuck in the lower branch.
With PAR and TEE: No SimpleTermination: there is no fairness that forces the transition -> NEE, the execution loops on AT while a token is stuck on the edge PAR->NEE.
With PAR and NEE: as above.
*/

check {Safe} for 0 but 15 State expect 0

check {SimpleTermination} for 0 but 20 State expect 1
check {CorrectTermination} for 0 but 20 State expect 1

run {Safe} for 0 but 11 State expect 1

// Do not verify NoLoopingEdge!
check WellFormed for 1 expect 1
