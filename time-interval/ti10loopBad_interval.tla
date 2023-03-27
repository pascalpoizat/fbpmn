---------------- MODULE ti10loopBad_interval ----------------
EXTENDS ti10loopBad
Interval == INSTANCE PWSIntervals
(* constraint *)
ConstraintAC == Interval!After("Task_C","Task_A")
================================================================
