---------------- MODULE PWSSemantics ----------------
EXTENDS Naturals, PWSTypes, PWSDefs, FiniteSets

CONSTANT Constraint, IntervalConstraint

VARIABLES
  edgemarks,
  nodemarks,
  net,
  lifecycle

var == <<nodemarks, edgemarks, net, lifecycle>>

LOCAL Network == INSTANCE Network

NoReEnter == TRUE

TypeInvariant ==
  /\ edgemarks \in [ Edge -> Nat ]
  /\ nodemarks \in [ Node -> Nat ]
  /\ lifecycle \in [ ActivableNode -> [ {"started","finished","active"} -> BOOLEAN ]]
  /\ Network!TypeInvariant

(* ---- conditions ---- *)

subprocess_may_complete(n) ==
  /\ CatN[n] = SubProcess
  /\ nodemarks[n] >= 1
  /\ \A e \in Edge : source[e] \in ContainRel[n] /\ target[e] \in ContainRel[n] => edgemarks[e] = 0
  /\ \E ee \in ContainRel[n] :
      /\ CatN[ee] \in EndEventType
      /\ nodemarks[ee] >= 1
  /\ \A x \in ContainRel[n] : CatN[x] \in EndEventType \/ nodemarks[x] = 0

(* ---- none start event ---- *)

LOCAL noneortimerstart_complete(n) ==
  /\ nodemarks[n] >= 1
  /\ LET p == ContainRelInv(n) IN
      \/ /\ CatN[p] = Process
         /\ nodemarks[p] = 0  \* No multi-instance
         /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1, ![p] = @ + 1 ]
      \/ /\ CatN[p] = SubProcess
         /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged
  
nonestart_complete(n) ==
  /\ CatN[n] = NoneStartEvent
  /\ noneortimerstart_complete(n)
  /\ UNCHANGED lifecycle

(* ---- timer start event ---- *)

timerstart_complete(n) ==
  /\ CatN[n] = TimerStartEvent
  /\ noneortimerstart_complete(n)
  /\ UNCHANGED lifecycle

(* ---- message start event ---- *)

messagestart_complete(n) ==
  /\ CatN[n] = MessageStartEvent
  /\ nodemarks[n] >= 1
  /\ \E em \in intype(MessageFlowType, n) :
     /\ edgemarks[em] >= 1
     /\ Network!receive(ProcessOf(source[em]), ProcessOf(n), msgtype[em])
     /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                         IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                         ELSE IF e = em THEN edgemarks[e] - 1
                         ELSE edgemarks[e] ]
  /\ \E p \in Processes :
     /\ n \in ContainRel[p]
     /\ nodemarks[p] = 0  \* No multi-instance
     /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1, ![p] = @ + 1 ]
  /\ UNCHANGED lifecycle

(* ---- none end event, terminate end event ---- *)

noneend_start(n) ==
  /\ CatN[n] = NoneEndEvent
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ Network!unchanged
  /\ UNCHANGED lifecycle

terminateend_start(n) == \* Terminate End Event clears all token in the process/subprocess (except for the n node).
  /\ CatN[n] = TerminateEndEvent
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ LET pr == ContainRelInv(n) IN
          LET includedNodes == ContainRelPlus(pr) IN
           /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                             IF source[ee] \in includedNodes /\ target[ee] \in includedNodes THEN 0
                             ELSE edgemarks[ee] ]
           /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                             IF nn = n THEN 1
                             ELSE IF nn \in includedNodes THEN 0
                             ELSE nodemarks[nn] ]
           /\ lifecycle' = [ nn \in DOMAIN lifecycle |->
                             IF nn \in includedNodes /\ lifecycle[nn].active THEN [ started |-> TRUE, finished |-> TRUE, active |-> FALSE ]
                             ELSE lifecycle[nn] ]
  /\ Network!unchanged

(* ---- message end event ---- *)

messageend_start(n) ==
  /\ CatN[n] = MessageEndEvent
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in outtype(MessageFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ Network!send(ProcessOf(n), ProcessOf(target[e2]), msgtype[e2])
     /\ edgemarks' = [ edgemarks EXCEPT ![e1] = @ - 1, ![e2] = @ + 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ UNCHANGED lifecycle

(* ---- TMIE / CMIE ---- *)

tmie_start(n) ==
  /\ CatN[n] = ThrowMessageIntermediateEvent
  /\ \E ein \in intype(SeqFlowType, n), eout \in outtype(MessageFlowType, n) :
      /\ edgemarks[ein] >= 1
      /\ Network!send(ProcessOf(n), ProcessOf(target[eout]), msgtype[eout])
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                           IF ee = ein THEN edgemarks[ee] - 1
                           ELSE IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                           ELSE IF ee = eout THEN edgemarks[ee] + 1
                           ELSE edgemarks[ee] ]
      /\ UNCHANGED nodemarks
      /\ UNCHANGED lifecycle

cmie_start(n) ==
  /\ CatN[n] = CatchMessageIntermediateEvent
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in intype(MessageFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ edgemarks[e2] >= 1
     /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
     /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                        IF e \in {e1,e2} THEN edgemarks[e] - 1
                        ELSE IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                        ELSE edgemarks[e] ]
     /\ UNCHANGED nodemarks
     /\ UNCHANGED lifecycle

(* ---- timer intermediate event ---- *)

tie_start(n) ==
  /\ CatN[n] = TimerIntermediateEvent
  /\ \E ein \in intype(SeqFlowType, n) :
     /\ edgemarks[ein] >= 1
     /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e = ein THEN edgemarks[e] - 1
                      ELSE IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
     /\ UNCHANGED nodemarks
     /\ Network!unchanged
     /\ UNCHANGED lifecycle

(* ---- message boundary event ---- *)

LOCAL mbe_start_subprocess_interrupting(n) ==
  /\ BoundaryEvent[n].cancelActivity (* interrupting *)
  /\ LET act == BoundaryEvent[n].attachedTo IN
     /\ CatN[act] = SubProcess
      /\ nodemarks[act] >= 1
      /\ ~ subprocess_may_complete(act)
      /\ \E e2 \in intype(MessageFlowType, n) :
        /\ edgemarks[e2] >= 1
        /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
        /\ LET includedNodes == ContainRelPlus(act) IN
                  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                                    IF nn = act THEN 0
                                    ELSE IF nn \in includedNodes THEN 0
                                    ELSE nodemarks[nn] ]
                  /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                    IF ee \in {e2} THEN edgemarks[ee] - 1
                                    ELSE IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                    ELSE IF source[ee] \in includedNodes /\ target[ee] \in includedNodes THEN 0
                                    ELSE edgemarks[ee] ]
                  /\ lifecycle' = [ nn \in DOMAIN lifecycle |->
                                    IF nn = act THEN [ started |-> TRUE, finished |-> TRUE, active |-> FALSE ]
                                    ELSE IF nn \in includedNodes /\ lifecycle[nn].active THEN [ started |-> TRUE, finished |-> TRUE, active |-> FALSE ]
                                    ELSE lifecycle[nn] ]
     
LOCAL mbe_start_subprocess_noninterrupting(n) ==
  /\ ~ BoundaryEvent[n].cancelActivity (* non-interrupting *)
  /\ LET act == BoundaryEvent[n].attachedTo IN
     /\ CatN[act] = SubProcess
      /\ nodemarks[act] >= 1
      /\ \E e2 \in intype(MessageFlowType, n) :
        /\ edgemarks[e2] >= 1
        /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
        /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                IF ee \in {e2} THEN edgemarks[ee] - 1
                                ELSE IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                ELSE edgemarks[ee] ]
        /\ UNCHANGED nodemarks
        /\ UNCHANGED lifecycle

LOCAL mbe_start_other(n) ==
  /\ LET act == BoundaryEvent[n].attachedTo IN
      /\ CatN[act] # SubProcess
      /\ nodemarks[act] >= 1
      /\ \E e2 \in intype(MessageFlowType, n) :
        /\ edgemarks[e2] >= 1
        /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
        /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                IF ee \in {e2} THEN edgemarks[ee] - 1
                                ELSE IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                ELSE edgemarks[ee] ]
        /\ IF BoundaryEvent[n].cancelActivity THEN (* interrupting *)
             /\ nodemarks' = [ nodemarks EXCEPT ![act] = 0 ]
             /\ lifecycle' = [ lifecycle EXCEPT ![act] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE ] ]
            ELSE (* non interrupting *)
              UNCHANGED <<nodemarks, lifecycle>>

mbe_start(n) ==
  /\ CatN[n] = MessageBoundaryEvent
  /\ \/ mbe_start_subprocess_interrupting(n)
     \/ mbe_start_subprocess_noninterrupting(n)
     \/ mbe_start_other(n)

(* ---- timer boundary event ---- *)

(* close to MBE, without the message edge. *)

LOCAL tbe_start_subprocess_interrupting(n) ==
  /\ BoundaryEvent[n].cancelActivity (* interrupting *)
  /\ LET act == BoundaryEvent[n].attachedTo IN
     /\ CatN[act] = SubProcess
      /\ nodemarks[act] >= 1
      /\ ~ subprocess_may_complete(act)
      /\ LET includedNodes == ContainRelPlus(act) IN
                  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                                    IF nn = act THEN 0
                                    ELSE IF nn \in includedNodes THEN 0
                                    ELSE nodemarks[nn] ]
                  /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                    IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                    ELSE IF source[ee] \in includedNodes /\ target[ee] \in includedNodes THEN 0
                                    ELSE edgemarks[ee] ]
                  /\ lifecycle' = [ nn \in DOMAIN lifecycle |->
                                    IF nn = act THEN [ started |-> TRUE, finished |-> TRUE, active |-> FALSE ]
                                    ELSE IF nn \in includedNodes /\ lifecycle[nn].active THEN [ started |-> TRUE, finished |-> TRUE, active |-> FALSE ]
                                    ELSE lifecycle[nn] ]

LOCAL tbe_start_subprocess_noninterrupting(n) ==
  /\ ~ BoundaryEvent[n].cancelActivity (* non-interrupting *)
  /\ LET act == BoundaryEvent[n].attachedTo IN
     /\ CatN[act] = SubProcess
      /\ nodemarks[act] >= 1
        /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                ELSE edgemarks[ee] ]
        /\ UNCHANGED nodemarks
        /\ UNCHANGED lifecycle

LOCAL tbe_start_other(n) ==
  /\ LET act == BoundaryEvent[n].attachedTo IN
      /\ CatN[act] # SubProcess
      /\ nodemarks[act] >= 1
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                                IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                                ELSE edgemarks[ee] ]
      /\ IF BoundaryEvent[n].cancelActivity THEN (* interrupting *)
             /\ nodemarks' = [ nodemarks EXCEPT ![act] = 0 ]
             /\ lifecycle' = [ lifecycle EXCEPT ![act] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE ] ]
         ELSE (* non interrupting *)
              UNCHANGED <<nodemarks, lifecycle>>

tbe_start(n) ==
  /\ CatN[n] = TimerBoundaryEvent
  /\ \/ tbe_start_subprocess_interrupting(n)
     \/ tbe_start_subprocess_noninterrupting(n)
     \/ tbe_start_other(n)
  /\ Network!unchanged

----------------------------------------------------------------

(* ---- Exclusive Or / XOR ---- *)

LOCAL xor_complete_out(n,eout) ==
  /\ \E ein \in intype(SeqFlowType, n) :
       /\ edgemarks[ein] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged
  /\ UNCHANGED lifecycle

xor_complete(n) ==
  /\ CatN[n] = ExclusiveOr
  /\ \E eout \in outtype(SeqFlowType, n) : \* eout may be Conditional or Default
         xor_complete_out(n, eout)

LOCAL xor_fairness(n) ==
   Cardinality(outtype(SeqFlowType, n)) > 1 =>
   \A eout \in outtype(SeqFlowType, n) : SF_var(xor_complete_out(n,eout))

(* ---- Parallel / AND ---- *)

parallel_complete(n) ==
  /\ CatN[n] = Parallel
  /\ \A e \in intype(SeqFlowType, n) : edgemarks[e] >= 1
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in intype(SeqFlowType, n) THEN edgemarks[e] - 1
                      ELSE IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged
  /\ UNCHANGED lifecycle

(* ---- Inclusive Or / OR ---- *)

LOCAL or_complete_outs(n, eouts) ==
  LET InPlus == { e \in intype(SeqFlowType, n) : edgemarks[e] >= 1 } IN
  LET InMinus == { e \in intype(SeqFlowType, n) : edgemarks[e] = 0 } IN
  LET ignoredpreedges == UNION { PreEdges(n,e) : e \in InPlus } IN
  LET ignoredprenodes == UNION { PreNodes(n,e) : e \in InPlus } IN
        /\ InPlus # {}
        /\ eouts # {}
        /\ \A ezero \in InMinus : /\ \A ee \in (PreEdges(n, ezero) \ ignoredpreedges) : edgemarks[ee] = 0
                                  /\ \A nn \in (PreNodes(n, ezero) \ ignoredprenodes) : nodemarks[nn] = 0
        /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                                   IF e \in InPlus THEN edgemarks[e] - 1
                                   ELSE IF e \in eouts THEN edgemarks[e] + 1
                                   ELSE edgemarks[e] ]
        /\ UNCHANGED nodemarks
        /\ UNCHANGED lifecycle
        /\ Network!unchanged

or_complete(n) ==
  /\ CatN[n] = InclusiveOr
  /\ \/ \E eouts \in SUBSET outtype({ NormalSeqFlow, ConditionalSeqFlow }, n) : or_complete_outs(n, eouts)
     \/ \E eout \in outtype({ DefaultSeqFlow }, n) : or_complete_outs(n, {eout})

LOCAL or_fairness(n) == \* fairness is also applied on DefaultSeqFlow
   Cardinality(outtype(SeqFlowType, n)) > 1 =>
     \A eout \in  outtype(SeqFlowType, n) : SF_var(or_complete_outs(n, {eout}))

(* ---- Event Based / EXOR ---- *)

LOCAL eventbased_complete_out(n, eout) ==
  /\ \E ein \in intype(SeqFlowType, n) :
      /\ edgemarks[ein] >= 1
      /\ \/ CatN[target[eout]] \in {ReceiveTask,CatchMessageIntermediateEvent} /\ \E emsg \in intype(MessageFlowType, target[eout]) : edgemarks[emsg] # 0
         \/ CatN[target[eout]] \in {TimerIntermediateEvent}
      /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged
  /\ UNCHANGED lifecycle

eventbased_complete(n) ==
  /\ CatN[n] = EventBased
  /\ \E eout \in outtype(SeqFlowType, n) : eventbased_complete_out(n, eout)

LOCAL eventbased_fairness(n) ==
   Cardinality(outtype(SeqFlowType, n)) > 1 =>
   \A eout \in outtype(SeqFlowType, n) : SF_var(eventbased_complete_out(n,eout))

----------------------------------------------------------------

(* ---- abstract task ---- *)

abstract_start(n) ==
  /\ CatN[n] = AbstractTask
  /\ (NoReEnter => nodemarks[n] = 0)
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.started = TRUE, !.active = TRUE ]]
  /\ Network!unchanged

abstract_complete(n) ==
  /\ CatN[n] = AbstractTask
  /\ nodemarks[n] >= 1
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE ]]
  /\ Network!unchanged

(* ---- send task ---- *)

send_start(n) ==
  /\ CatN[n] = SendTask
  /\ (NoReEnter => nodemarks[n] = 0)
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.started = TRUE, !.active = TRUE ]]
  /\ Network!unchanged

send_complete(n) ==
  /\ CatN[n] = SendTask
  /\ nodemarks[n] >= 1
  /\ \E e \in outtype(MessageFlowType, n) :
      /\ Network!send(ProcessOf(n), ProcessOf(target[e]), msgtype[e])
      /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                           IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                           ELSE IF ee = e THEN edgemarks[ee] + 1
                           ELSE edgemarks[ee] ]
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE  ]]

(* ---- receive task ---- *)

receive_start(n) ==
  /\ CatN[n] = ReceiveTask
  /\ (NoReEnter => nodemarks[n] = 0)
  /\ \E e \in intype(SeqFlowType, n) :
     /\ edgemarks[e] >= 1
     /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ Network!unchanged
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.started = TRUE, !.active = TRUE ]]

receive_complete(n) ==
  /\ CatN[n] = ReceiveTask
  /\ nodemarks[n] >= 1
  /\ \E e \in intype(MessageFlowType, n) :
      /\ edgemarks[e] >= 1
      /\ Network!receive(ProcessOf(source[e]), ProcessOf(n), msgtype[e])
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                          IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                          ELSE IF ee = e THEN edgemarks[ee] - 1
                          ELSE edgemarks[ee] ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE  ]]

(* ---- SubProcess ---- *)

subprocess_start(n) ==
  /\ CatN[n] = SubProcess
  /\ (NoReEnter => nodemarks[n] = 0)
  /\ \E e \in intype(SeqFlowType, n) :
     /\ edgemarks[e] >= 1
     /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                       IF nn = n THEN nodemarks[nn] + 1
                       ELSE IF nn \in ContainRel[n] /\ CatN[nn] \in StartEventType THEN nodemarks[nn] + 1
                       ELSE nodemarks[nn] ]
  /\ Network!unchanged
  /\ lifecycle' = [ nn \in DOMAIN lifecycle |->
                       IF nn = n THEN [ started |-> TRUE, finished |-> FALSE, active |-> TRUE ]
                       ELSE IF nn \in ContainRel[n] THEN [ started |-> FALSE, finished |-> FALSE, active |-> FALSE ]
                       ELSE lifecycle[nn] ]

subprocess_complete(n) ==
  /\ CatN[n] = SubProcess
  /\ nodemarks[n] >= 1
  /\ \A e \in Edge : source[e] \in ContainRel[n] /\ target[e] \in ContainRel[n] => edgemarks[e] = 0
  /\ \E ee \in ContainRel[n] :
      /\ CatN[ee] \in EndEventType
      /\ nodemarks[ee] >= 1
  /\ \A x \in ContainRel[n] : nodemarks[x] >= 1 => CatN[x] \in EndEventType
  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                      IF nn = n THEN 0 
                      ELSE IF nn \in ContainRel[n] /\ CatN[nn] \in EndEventType THEN 0
                      ELSE nodemarks[nn] ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged
  /\ lifecycle' = [ lifecycle EXCEPT ![n] = [ @ EXCEPT !.finished = TRUE, !.active = FALSE  ]]

(* ---- Top level Process ---- *)

process_complete(n) == FALSE

----------------------------------------------------------------

step(n) ==
  CASE CatN[n] = NoneStartEvent -> nonestart_complete(n)
    [] CatN[n] = TimerStartEvent -> timerstart_complete(n)
    [] CatN[n] = MessageStartEvent -> messagestart_complete(n)
    [] CatN[n] = NoneEndEvent -> noneend_start(n)
    [] CatN[n] = TerminateEndEvent -> terminateend_start(n)
    [] CatN[n] = MessageEndEvent -> messageend_start(n)
    [] CatN[n] = AbstractTask -> abstract_start(n) \/ abstract_complete(n)
    [] CatN[n] = SendTask -> send_start(n) \/ send_complete(n)
    [] CatN[n] = ReceiveTask -> receive_start(n) \/ receive_complete(n)
    [] CatN[n] = ThrowMessageIntermediateEvent -> tmie_start(n)
    [] CatN[n] = CatchMessageIntermediateEvent -> cmie_start(n)
    [] CatN[n] = TimerIntermediateEvent -> tie_start(n)
    [] CatN[n] = MessageBoundaryEvent -> mbe_start(n)
    [] CatN[n] = TimerBoundaryEvent -> tbe_start(n)
    [] CatN[n] = SubProcess -> subprocess_start(n) \/ subprocess_complete(n)
    [] CatN[n] = ExclusiveOr -> xor_complete(n)
    [] CatN[n] = InclusiveOr -> or_complete(n)
    [] CatN[n] = Parallel -> parallel_complete(n)
    [] CatN[n] = EventBased -> eventbased_complete(n)
    [] CatN[n] = Process -> process_complete(n)

Next == \E n \in Node : step(n)

Init ==
  /\ nodemarks = [ n \in Node |->
                     IF CatN[n] \in StartEventType /\ (\E p \in Processes : n \in ContainRel[p]) THEN 1
                     ELSE 0 ]
  /\ edgemarks = [ e \in Edge |-> 0 ]
  /\ lifecycle = [ n \in ActivableNode |-> [ started |-> FALSE, finished |-> FALSE, active |-> FALSE ]]
  /\ Network!init

Fairness_Next == \A n \in Node : WF_var(step(n))

Fairness_Gateway ==
  /\ \A n \in Node : CatN[n] = ExclusiveOr => xor_fairness(n)
  /\ \A n \in Node : CatN[n] = EventBased => eventbased_fairness(n)
  /\ \A n \in Node : CatN[n] = InclusiveOr => or_fairness(n)

Fairness == Fairness_Next /\ Fairness_Gateway

Spec == Init /\ [][Next /\ Constraint' /\ IntervalConstraint']_var /\ Fairness

(* ---------------------------------------------------------------- *)

(* Correction properties *)

(* Every task may be enabled (in some executions).
   A possibility property => we check the *failure* of the following property *)
(* Bug TLC: one needs to manually expand the disjonction and check individually each case. *)
OneNodeNeverActive == LET tasks == { p \in Node : CatN[p] \in TaskType } IN
                       \E n \in tasks : [](nodemarks[n] = 0)

(* Simple Termination: an EndEvent occurs for each process *)
SimpleTermination ==
  \A p \in Processes : <>(\E n \in ContainRel[p] : CatN[n] \in EndEventType /\ nodemarks[n] > 0)

(* Correct termination: SimpleTermination + no token left in the process *)
CorrectTermination ==
  \A p \in Processes : <>(\E n \in ContainRel[p] : /\ CatN[n] \in EndEventType
                                                   /\ nodemarks[n] > 0
                                                   /\ \A nn \in ContainRel[p] \ {n} : nodemarks[nn] = 0)

(* No abnormal termination = TerminateEndEvent never activated. *)
NoAbnormalTermination ==
  \A n \in Node : CatN[n] = TerminateEndEvent => [](nodemarks[n] = 0)

(* No messages are eventually left in transit. *)
NoUndeliveredMessages == <>[](LET msgflows == { ee \in Edge : CatE[ee] \in MessageFlowType } IN
                                   \A e \in msgflows : edgemarks[e] = 0)

\* Any message is eventually delivered.
\* NoUndeliveredMessages2 ==
\*  \A m \in Processes \X Processes \X Message : [](Network!intransit(m) => <>(~ Network!intransit(m)))

(* ---------------------------------------------------------------- *)

(* Correctness properties from F. Corradini, C. Muzi, B. Re, and F. Tiezzi, « A Classification of BPMN Collaborations based on Safeness and Soundness Notions », EXPRESS/SOS’18. *)
(* They have been adapted to our marking, where both edges and nodes hold tokens. *)

(* No sequence flow edge has more than one token. *)
SafeCollaboration ==
   [](\A e \in Edge : CatE[e] \in SeqFlowType => edgemarks[e] <= 1)

(* A process is sound if there are no token on inside edges, and one token only on EndEvents. Start events are ignored. *)
LOCAL SoundProcessInt(p) ==
   /\ \A e \in Edge : source[e] \in ContainRel[p] /\ target[e] \in ContainRel[p] => edgemarks[e] = 0
   /\ \A n \in ContainRel[p] :
            \/ CatN[n] \in StartEventType
            \/ nodemarks[n] = 0
            \/ nodemarks[n] = 1 /\ CatN[n] \in EndEventType

SoundProcess(p) == <> SoundProcessInt(p)

(* All processes are sound and there are no undelivered messages. *)
SoundCollaboration ==
   <>[](/\ \A n \in Node : CatN[n] = Process => SoundProcessInt(n)
        /\ \A e \in Edge : CatE[e] \in MessageFlowType => edgemarks[e] = 0)

(* Like SoundCollaboration, but ignore messages in transit. *)
MessageRelaxedSoundCollaboration ==
   <>[](\A n \in Node : CatN[n] = Process => SoundProcessInt(n))

================================================================
