---------------- MODULE PWSIntervals ----------------
VARIABLE lifecycle 

AafterB(A,B) == lifecycle[A].started => lifecycle[B].completed

AbeforeB(A,B) == lifecycle[B].started => lifecycle[A].completed

AexclusiveB(A,B) == ~(lifecycle[A].active /\ lifecycle[B].active)

(* A overlaps B *)
BstartsWithinA(A,B) == /\ ~(lifecycle[B].started /\ ~lifecycle[A].started)
                       /\ ~(lifecycle[A].completed /\ ~lifecycle[B].started)

BduringA(A,B) == /\ (lifecycle[B].started => lifecycle[A].started)
                 /\ (lifecycle[A].completed => lifecycle[B].completed)

================================================================
