/*
A process:
NSE -> (PAR or XOR) -> (NEE or TEE)
             |_> AT loop
*/
module example3

open PWSSyntax

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

