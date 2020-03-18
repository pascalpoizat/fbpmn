/*
A process:
{NSE,TSE} -> AT -> NEE
*/
module example1

open PWSSyntax
open PWSProp

one sig at extends AbstractTask {}
one sig se extends NoneStartEvent {}
one sig ee extends NoneEndEvent {}

one sig f1 extends NormalSequentialFlow {} {
    source = se
    target = at
}
one sig f2 extends NormalSequentialFlow {} {
    source = at
    target = ee
}

one sig p1 extends Process {} {
    contains = se + at + ee
}

