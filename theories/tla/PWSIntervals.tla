---------------- MODULE PWSIntervals ----------------
VARIABLE lifecycle 

(* A starts after B is completed. Allows A to never start. *)
After(A,B) == lifecycle[A].started => lifecycle[B].completed

(* A completes before B starts. Allows B to never start. *)
(* Before(A,B) = ~After(B,A) if both starts. *)
Before(A,B) == lifecycle[B].started => lifecycle[A].completed

(* Both activities cannot be simultaneously active. *)
Exclusive(A,B) == ~(lifecycle[A].active /\ lifecycle[B].active)

(* A overlaps B: A starts first, B starts before A completes. *)
(* Allows B to never start if A never completes. *)
StartsWithin(A,B) == /\ ~(lifecycle[B].started /\ ~lifecycle[A].started)
                      /\ ~(lifecycle[A].completed /\ ~lifecycle[B].started)

(* B is fully inside A. *)
During(A,B) == /\ (lifecycle[B].started => lifecycle[A].started)
               /\ (lifecycle[A].completed => lifecycle[B].completed)

================================================================
