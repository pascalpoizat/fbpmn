---------------- MODULE ti01wf_interval ----------------

(* Must fail first assumption *)

EXTENDS ti01wf

Interval == INSTANCE PWSIntervals

ConstraintAB == Interval!During("A","B")

ASSUME Interval!WellFormed_EndsWithin_1("A","B")
ASSUME Interval!WellFormed_EndsWithin_2("A","B")
ASSUME Interval!WellFormed_EndsWithin_3("A","B")

================================================================

