---------------- MODULE ti11loopGood_interval ----------------

EXTENDS ti11loopGood

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintAC == Interval!After("Activity_C","Activity_Astar")

================================================================
