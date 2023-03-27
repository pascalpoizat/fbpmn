---------------- MODULE ti19OnlineOrdering_interval ----------------
EXTENDS ti19OnlineOrdering
Interval == INSTANCE PWSIntervals
ConstraintI == Interval!After("sms","email") /\ Interval!Overlaps("packageItems","generateTrackingInfo")

Prop == []Interval!Before("Payment","transport")

================================================================
