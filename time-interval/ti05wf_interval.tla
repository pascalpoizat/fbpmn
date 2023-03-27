---------------- MODULE ti05wf_interval ----------------
(* Must fail first assumption *)
EXTENDS ti05wf
Interval == INSTANCE PWSIntervals

ASSUME Interval!WellFormed_EndsWithin_1("B","A")
ASSUME Interval!WellFormed_EndsWithin_2("B","A")
ASSUME Interval!WellFormed_EndsWithin_3("B","A")
================================================================
