---------------- MODULE ti28Comm_interval ----------------
EXTENDS ti28Comm
Interval == INSTANCE PWSIntervals
ConstraintI == /\ Interval!During("ST1", "RT1")
               /\ Interval!During("ST2", "RT2")
               /\ Interval!During("ST3", "RT3")
================================================================
