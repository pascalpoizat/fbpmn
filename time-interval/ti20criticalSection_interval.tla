---------------- MODULE ti20criticalSection_interval ----------------

EXTENDS ti20criticalSection

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintCS == Interval!Exclusive("C", "D")

(* checked property *)
ExclusiveCS == []Interval!Exclusive("C", "D")

================================================================
