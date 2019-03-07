---------------- MODULE PWSSemantics ----------------

EXTENDS Naturals, PWSTypes, PWSDefs

VARIABLES
  edgemarks,
  nodemarks,
  net

var == <<nodemarks, edgemarks, net>>

LOCAL Network == INSTANCE Network

TypeInvariant ==
  /\ edgemarks \in [ Edge -> Nat ]
  /\ nodemarks \in [ Node -> Nat ]
  /\ Network!TypeInvariant

(* ---- none start event ---- *)

nonestart_complete(n) ==
  /\ CatN[n] = NoneStartEvent
  /\ nodemarks[n] >= 1
  /\ \E p \in Processes :
     /\ n \in ContainRel[p]
     /\ nodemarks[p] = 0  \* XXXX No multi-instance XXXX
     /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1, ![p] = @ + 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- message start event ---- *)

messagestart_start(n) ==
  /\ CatN[n] = MessageStartEvent
  /\ nodemarks[n] = 0
  /\ \E e \in intype(MsgFlowType, n) :
     /\ edgemarks[e] >= 1
     /\ Network!receive(ProcessOf(source[e]), ProcessOf(n), msgtype[e])
     /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]

messagestart_complete(n) ==
  /\ CatN[n] = MessageStartEvent
  /\ nodemarks[n] >= 1
  /\ \E p \in Processes :
     /\ n \in ContainRel[p]
     /\ nodemarks[p] = 0  \* XXXX No multi-instance XXXX
     /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1, ![p] = @ + 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- none end event, terminate end event ---- *)

noneend_start(n) ==
  /\ CatN[n] = NoneEndEvent
  \* /\ nodemarks[n] = 0 \* why is it necessary for Terminate End but not for None End?
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = 1 ]
  /\ Network!unchanged

terminateend_start(n) ==
  /\ CatN[n] = TerminateEndEvent
  /\ nodemarks[n] = 0
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = 1 ]
  /\ Network!unchanged

(* ---- message end event ---- *)

messageend_start(n) ==
  /\ CatN[n] = MessageEndEvent
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in outtype(MsgFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ Network!send(ProcessOf(n), ProcessOf(target[e2]), msgtype[e2])
     /\ edgemarks' = [ edgemarks EXCEPT ![e1] = @ - 1, ![e2] = @ + 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = 1 ]

(* ---- abstract task ---- *)

abstract_start(n) ==
  /\ CatN[n] = AbstractTask
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
  /\ Network!unchanged

abstract_complete(n) ==
  /\ CatN[n] = AbstractTask
  /\ nodemarks[n] >= 1
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- send task ---- *)

send_start(n) ==
  /\ CatN[n] = SendTask
  /\ nodemarks[n] = 0
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = 1 ]
  /\ Network!unchanged
       
send_complete(n) ==
  /\ CatN[n] = SendTask
  /\ nodemarks[n] >= 1
  /\ \E e \in outtype(MsgFlowType, n) :
      /\ Network!send(ProcessOf(n), ProcessOf(target[e]), msgtype[e])
      /\ nodemarks' = [ nodemarks EXCEPT ![n] = 0 ]
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                           IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                           ELSE IF ee = e THEN edgemarks[ee] + 1
                           ELSE edgemarks[ee] ]

(* ---- receive task ---- *)

receive_start(n) ==
  /\ CatN[n] = ReceiveTask
  /\ nodemarks[n] = 0
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in intype(MsgFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ edgemarks[e2] >= 1
     /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
     /\ edgemarks' = [ edgemarks EXCEPT ![e1] = @ - 1, ![e2] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]

receive_complete(n) ==
  /\ CatN[n] = ReceiveTask
  /\ nodemarks[n] >= 1
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- TMIE / CMIE ---- *)

tmie_start(n) ==
  /\ CatN[n] = ThrowMessageIntermediateEvent
  /\ \E ein \in intype(SeqFlowType, n), eout \in outtype(MsgFlowType, n) :
      /\ edgemarks[ein] >= 1
      /\ Network!send(ProcessOf(n), ProcessOf(target[eout]), msgtype[eout])
      /\ edgemarks' = [ ee \in DOMAIN edgemarks |->
                           IF ee = ein THEN edgemarks[ee] - 1
                           ELSE IF ee \in outtype(SeqFlowType, n) THEN edgemarks[ee] + 1
                           ELSE IF ee = eout THEN edgemarks[ee] + 1
                           ELSE edgemarks[ee] ]

cmie_start(n) == 
  /\ CatN[n] = CatchMessageIntermediateEvent
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in intype(MsgFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ edgemarks[e2] >= 1
     /\ Network!receive(ProcessOf(source[e2]), ProcessOf(n), msgtype[e2])
     /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                        IF e \in {e1,e2} THEN edgemarks[e] - 1
                        ELSE IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                        ELSE edgemarks[e] ]
     /\ UNCHANGED nodemarks

(* ---- SubProcess ---- *)

subprocess_start(n) ==
  /\ CatN[n] = SubProcess
  /\ nodemarks[n] = 0
  /\ \E e \in intype(SeqFlowType, n) :
     /\ edgemarks[e] >= 1
     /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                       IF nn = n THEN 1
                       ELSE IF nn \in ContainRel[n] /\ CatN[nn] \in StartEventType THEN 1
                       ELSE nodemarks[nn] ]
  /\ Network!unchanged

subprocess_complete(n) == 
  /\ CatN[n] = SubProcess
  /\ nodemarks[n] = 1
  /\ \A x \in ContainRel[n] : CatN[x] \notin EndEventType => nodemarks[x] = 0
  /\ \E nee \in ContainRel[n] :
      /\ CatN[nee] \in EndEventType
      /\ nodemarks[nee] = 1
      /\ nodemarks' = [ nodemarks EXCEPT ![n] = 0, ![nee] = 0 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- Exclusive Or ---- *)

xor_complete(n) ==
  /\ CatN[n] = ExclusiveOr
  /\ \E ein \in intype(SeqFlowType, n), eout \in outtype(SeqFlowType, n) : \* eout may be Conditional or Default
       /\ edgemarks[ein] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged

(* ---- Inclusive Or ---- *)

or_complete(n) ==
  /\ CatN[n] = InclusiveOr
  /\ LET InPlus == { e \in intype(SeqFlowType, n) : edgemarks[e] >= 1 } IN
     LET InMinus == { e \in intype(SeqFlowType, n) : edgemarks[e] = 0 } IN
     LET ignoredpreedges == UNION { PreEdges(n,e) : e \in InPlus } IN
     LET ignoredprenodes == UNION { PreNodes(n,e) : e \in InPlus } IN
        /\ InPlus # {}
        /\ \A ezero \in InMinus : /\ \A ee \in (PreEdges(n, ezero) \ ignoredpreedges) : edgemarks[ee] = 0
                                  /\ \A nn \in (PreNodes(n, ezero) \ ignoredprenodes) : nodemarks[nn] = 0
        /\ \/ \E eouts \in SUBSET outtype({ NormalSeqFlow, ConditionalSeqFlow }, n) :
                 /\ eouts # {}
                 /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                                   IF e \in InPlus THEN edgemarks[e] - 1
                                   ELSE IF e \in eouts THEN edgemarks[e] + 1
                                   ELSE edgemarks[e] ]
                 /\ UNCHANGED nodemarks
                 /\ Network!unchanged
           \/ \E eout \in outtype({ DefaultSeqFlow }, n) :
                 /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                                   IF e \in InPlus THEN edgemarks[e] - 1
                                   ELSE IF e = eout THEN edgemarks[e] + 1
                                   ELSE edgemarks[e] ]
                 /\ UNCHANGED nodemarks
                 /\ Network!unchanged

(* ---- Parallel ---- *)

parallel_complete(n) ==
  /\ CatN[n] = Parallel
  /\ \A e \in intype(SeqFlowType, n) : edgemarks[e] >= 1
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in intype(SeqFlowType, n) THEN edgemarks[e] - 1
                      ELSE IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged

(* ---- Event Based ---- *)

eventbased_complete(n) ==
  /\ CatN[n] = EventBasedGateway
  /\ \E ein \in intype(SeqFlowType, n), eout \in outtype(SeqFlowType, n) :
      /\ edgemarks[ein] >= 1
      /\ \E emsg \in intype(MsgFlowType, target[eout]) : edgemarks[emsg] # 0
      /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged

(* ---- Top level Process ---- *)

LOCAL process_complete1(n) ==   
  /\ nodemarks[n] = 1
  /\ \E tee \in ContainRel[n] :
      /\ CatN[tee] = TerminateEndEvent
      /\ nodemarks[tee] = 1
      /\ nodemarks' = [ x \in DOMAIN nodemarks |->
                          IF x = n THEN 0
                          ELSE IF x = tee THEN 0
                          ELSE nodemarks[x] ]
  /\ UNCHANGED edgemarks
  /\ Network!unchanged

LOCAL process_complete2(n) ==
  /\ nodemarks[n] = 1
  /\ \E nee \in ContainRel[n] :
      /\ CatN[nee] = NoneEndEvent
      /\ nodemarks[nee] = 1
      /\ \A x \in ContainRel[n] : CatN[x] = NoneEndEvent /\ x # nee => nodemarks[x] = 0
      /\ nodemarks' = [ x \in DOMAIN nodemarks |->
                          IF x = n THEN 0
                          ELSE IF x = nee THEN 0
                          ELSE nodemarks[x] ]
  /\ UNCHANGED edgemarks
  /\ Network!unchanged

process_complete(n) ==
  /\ CatN[n] = Process
  /\ process_complete1(n) \/ process_complete2(n)

(* ---------------------------------------------------------------- *)

step(n) ==
  CASE CatN[n] = NoneStartEvent -> nonestart_complete(n)
    [] CatN[n] = MessageStartEvent -> messagestart_start(n) \/ messagestart_complete(n)
    [] CatN[n] = NoneEndEvent -> noneend_start(n)
    [] CatN[n] = TerminateEndEvent -> terminateend_start(n)
    [] CatN[n] = MessageEndEvent -> messageend_start(n)
    [] CatN[n] = AbstractTask -> abstract_start(n) \/ abstract_complete(n)
    [] CatN[n] = SendTask -> send_start(n) \/ send_complete(n)
    [] CatN[n] = ReceiveTask -> receive_start(n) \/ receive_complete(n)
    [] CatN[n] = ThrowMessageIntermediateEvent -> tmie_start(n)
    [] CatN[n] = CatchMessageIntermediateEvent -> cmie_start(n)
    [] CatN[n] = SubProcess -> subprocess_start(n) \/ subprocess_complete(n)
    [] CatN[n] = ExclusiveOr -> xor_complete(n)
    [] CatN[n] = InclusiveOr -> or_complete(n)
    [] CatN[n] = Parallel -> parallel_complete(n)
    [] CatN[n] = EventBasedGateway -> eventbased_complete(n)
    [] CatN[n] = Process -> process_complete(n)

Next == \E n \in Node : step(n)

Init ==
  /\ nodemarks = [ n \in Node |->
                     IF CatN[n] = NoneStartEvent /\ (\E p \in Processes : n \in ContainRel[p]) THEN 1
                     ELSE 0 ]
  /\ edgemarks = [ e \in Edge |-> 0 ]
  /\ Network!init

Spec == Init /\ [][Next]_var /\ WF_var(Next)

(* ---------------------------------------------------------------- *)

(* Correction properties *)

(* Every task may be enabled (in some executions).
   A possibility property => we check the *failure* of the following property *)
(* Bug TLC: one needs to manually expand the disjonction. *)
OneNodeNeverActive == \E n \in { p \in Node : CatN[p] \in TaskType } : [](nodemarks[n] = 0)

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

(* When all processes have ended, there are no messages left in transit. *)
NoUndeliveredMessages ==
  []((\A p \in Processes : nodemarks[p] = 0) => (\A e \in Edge : CatE[e] = MsgFlow => edgemarks[e] = 0))
  
================================================================
