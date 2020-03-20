open example8 as m
open PWSSemantics
open PWSProp

check {Safe} for 0 but 7 Int, 10 State

check {SimpleTermination} for 0 but 9 State
check {CorrectTermination} for 0 but 9 State

/* Bug : inconsistent with 8 State.
 * En State$6, PWSSemantics/State$6.cancompleteTimerIntermediateEvent[ti] est vrai
 * mais completeTimerIntermediateEvent[ti] ne semble pas être possible.
 * Je ne comprends pas pourquoi.
 */
run {Safe} for 0 but 8 State



