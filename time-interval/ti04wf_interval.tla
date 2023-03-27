---------------- MODULE ti04wf_interval ----------------

(* Must fail third assumption *)

EXTENDS ti04wf

Interval == INSTANCE PWSIntervals

ConstraintAB == Interval!During("Task_A","Task_B")

ASSUME Interval!WellFormed_EndsWithin_1("Task_A","Task_B")
ASSUME Interval!WellFormed_EndsWithin_2("Task_A","Task_B")
ASSUME Interval!WellFormed_EndsWithin_3("Task_A","Task_B")

================================================================

