---------------- MODULE ti13loopGood_interval ----------------

EXTENDS ti13loopGood

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintAB == Interval!Before("Activity_A","Activity_B")

================================================================
