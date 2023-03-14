---------------- MODULE PWSIntervals ----------------

(* Simplified lifecycle of an activity: an activity starts (after which it
is "started"), is "active", until it finishes (is "finished"). An activity
can finish by completion (normal end) or termination (interrupting boundary
event) ; these two cases are not distinguished. *)

EXTENDS PWSDefs, PWSTypes (* needed to check for well-formedness *)

VARIABLE lifecycle

(* A after B : A starts after B is finished. Allows A to never start. *)
After(A,B) == lifecycle[A].started => lifecycle[B].finished

(* A before B : A finishes before B starts. Allows B to never start. *)
Before(A,B) == After(B,A)

(* A and B exclusive : both activities cannot be simultaneously active. *)
Exclusive(A,B) == ~(lifecycle[A].active /\ lifecycle[B].active)

(* A starts within B: A starts between B start and B end. *)
(* Allows A to never start if B never finishes. *)
StartsWithin(A,B) == /\ (lifecycle[A].started => lifecycle[B].started)
                     /\ (lifecycle[B].finished => lifecycle[A].started)

(* A finishes within B: A finishes between B start and B end. *)
(* Allows B to never start if A never finishes. *)
EndsWithin(A,B) == /\ (lifecycle[A].finished => lifecycle[B].started)
                   /\ (lifecycle[B].finished => lifecycle[A].finished)

(* A overlaps B: A starts, B starts, A finishes, B finishes. *)
(* Allows B to never start if A never finishes. *)
Overlaps(A,B) == /\ StartsWithin(B,A)
                 /\ EndsWithin(A,B)

(* A during B: A is fully inside B. *)
(* Allows A to never start if B never finishes. *)
During(A,B) == /\ (lifecycle[A].started => lifecycle[B].started)
               /\ (lifecycle[B].finished => lifecycle[A].finished)

(* A contains B: B is fully inside A. *)
(* Allows B to never start if A never finishes. *)
Contains(A,B) == During(B,A)

----------------------------------------------------------------

(* An activity is Cancellable if it has an interrupting boundary event. *)
LOCAL Cancellable(a) ==
      \E be \in DOMAIN BoundaryEvent : (BoundaryEvent[be].attachedTo = a /\  BoundaryEvent[be].cancelActivity)

(* A subprocess is terminable if it contains a Terminate End Event. *)
LOCAL Terminable(p) == /\ CatN[p] = SubProcess
                       /\ \E n \in ContainRel[p] : CatN[n] = TerminateEndEvent

(* if "A endswithin B", then B should not be cancelled by a (direct) boundary event. *)
(* This includes "A during B" as "A during B" => "A endswithin B". *)
WellFormed_EndsWithin_1(A,B) == ~Cancellable(B)

(* If "A endswithin B", then B should not be indirectly cancelled by a cancelling subprocess, except if A is also in this subprocess. *)
WellFormed_EndsWithin_2(A,B) ==
   /\ ~\E p \in Node :
          /\ CatN[p] = SubProcess
          /\ Cancellable(p)
          /\ B \in ContainRelPlus(p)
          /\ A \notin ContainRelPlus(p)

(* If "A endswithin B", then B should not be indirectly cancelled by a terminating subprocess, except if A is also in this subprocess. *)
WellFormed_EndsWithin_3(A,B) ==
   /\ ~\E p \in Node :
          /\ CatN[p] = SubProcess
          /\ Terminable(p)
          /\ B \in ContainRelPlus(p)
          /\ A \notin ContainRelPlus(p)


================================================================
