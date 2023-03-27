---------------- MODULE ti16messages_interval ----------------
(* ti15messages works fine with NetworkBag, but deadlocks with NetworkFifoPair (if m2 is sent before m1).
   ti15messages_interval with the constraint Before("SendMessage1", "SendMessage2") works fine with NetworkFifoPair *)

EXTENDS ti16messages

Interval == INSTANCE PWSIntervals

(* constraint *)
ConstraintMessages == Interval!Before("SendMessage1", "SendMessage2")

(* checked property *)
Ordering == [](Interval!Before("ReceiveMessage1", "ReceiveMessage2") \/ Interval!EndsWithin("ReceiveMessage1", "ReceiveMessage2"))

================================================================
