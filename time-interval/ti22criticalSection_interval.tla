---------------- MODULE ti22criticalSection_interval ----------------

EXTENDS ti22criticalSection

Interval == INSTANCE PWSIntervals

(* checked property *)
ExclusiveCD == []Interval!Exclusive("C", "D")


================================================================
