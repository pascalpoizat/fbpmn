---------------- MODULE ti17OrTest_interval ----------------
EXTENDS ti17OrTest
Interval == INSTANCE PWSIntervals

Constraint23 == Interval!During("AT2", "AT3")

Prop == []Interval!After("AT5", "AT4")
================================================================
