---------------- MODULE ti14before_interval ----------------

EXTENDS ti14before

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintAB == Interval!StartsWithin("Task_A", "Task_B")

(* checked property *)
OrderingAC == []Interval!Before("Task_A", "Task_C")

================================================================
