---------------- MODULE ti18OrSize2x2_interval ----------------
EXTENDS ti18OrSize2x2
Interval == INSTANCE PWSIntervals

ConstraintI == Interval!During("A1", "A2") /\ Interval!Exclusive("A1","B1") /\ Interval!After("B1","B2")

================================================================
