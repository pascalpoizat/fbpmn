---------------- MODULE ti12loopBad_interval ----------------

EXTENDS ti12loopBad

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintAB == Interval!Before("Activity_A","Activity_B")

================================================================
