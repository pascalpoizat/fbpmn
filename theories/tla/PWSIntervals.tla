---------------- MODULE PWSIntervals ----------------
VARIABLE lifecycle 

AafterB(A,B) == lifecycle[A].started => lifecycle[B].finished

AbeforeB(A,B) == lifecycle[B].started => lifecycle[A].finished

AexclusiveB(A,B) == ~(lifecycle[A].active /\ lifecycle[B].active)

(* A overlaps B *)
BstartsWithinA(A,B) == /\ ~(lifecycle[B].started /\ ~lifecycle[A].started)
                       /\ ~(lifecycle[A].finished /\ ~lifecycle[B].started)

BduringA(A,B) == /\ (lifecycle[B].started => lifecycle[A].started)
                 /\ (lifecycle[A].finished => lifecycle[B].finished)

================================================================
