open example6 as m
open PWSSemantics
open PWSProp
open PWSWellformed

/*
CorrectTermination with 10 states

EmptyNetTermination should be invalid (by taking the TICE branch)
but :
  - it is indeed invalid with the non deterministic time.
  - it is (wrongly) valid with the explicit time, because
    time advances only when no step can be done.
    Here RT is enabled (because ST was enabled and thus was done) :
    the lower branch is never taken. Time increases only
    when deadlocked, everything is finished, and
    time can become > 4 only at that point.
I cannot imagine a solution (without fairness).
*/

check {Safe} for 0 but 10 State expect 0

check {SimpleTermination} for 0 but 10 State expect 0
check {CorrectTermination} for 0 but 10 State expect 0

// should be consistent but is not
run {! EmptyNetTermination} for 0 but 20 State expect 1

/* As EmptyNet : ee2b should be reachable, but is not for the same reason. */
/* This should be consistent, and it is not. */
run { some s: State | s.nodemarks[ee2b] = 1 } for 0 but 7 State expect 1

run {Safe} for 0 but 6 Int, 20 State expect 0

check WellFormed for 1 expect 0
