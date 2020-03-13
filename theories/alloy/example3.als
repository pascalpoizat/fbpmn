/*
A process:
NSE -> (PAR or XOR) -> (NEE or TEE)
             |_> AT loop

With XOR and NEE/TEE: No SimpleTermination, as it can get stuck in the lower branch.
With PAR and TEE: No SimpleTermination: there is no fairness that forces the transition -> NEE, the token stays on the edge PAR->NEE.
With PAR and NEE: as above.
*/


open PWSSyntax
open PWSProp

one sig at extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends TerminateEndEvent {}
one sig g1 extends Parallel {}

one sig f1 extends NormalSequentialFlow {} {
    source = se
    target = g1
}
one sig f2 extends NormalSequentialFlow {} {
    source = g1
    target = ee
}
one sig f3 extends NormalSequentialFlow {} {
    source = g1
    target = at
}
one sig f4 extends NormalSequentialFlow {} {
    source = at
    target = at
}

one sig proc extends Process {} {
    contains = se + g1 + at + ee
}

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 20 State
check {CorrectTermination} for 0 but 20 State

run {Safe} for 0 but 11 State
