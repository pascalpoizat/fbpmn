---------------- MODULE ti21criticalSection_interval ----------------

EXTENDS ti21criticalSection

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintCS == Interval!Exclusive("CS1", "CS2")

(* checked property *)
ExclusiveCS == []Interval!Exclusive("B", "F")

================================================================
