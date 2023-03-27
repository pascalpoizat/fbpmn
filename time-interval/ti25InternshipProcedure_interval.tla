---------------- MODULE ti25InternshipProcedure_interval ----------------
EXTENDS ti25InternshipProcedure
Interval == INSTANCE PWSIntervals
ConstraintI == Interval!After("Assign_Tutor","Notify_Delegate") /\ Interval!During("Accept_Internship", "Do_Internship")
================================================================
