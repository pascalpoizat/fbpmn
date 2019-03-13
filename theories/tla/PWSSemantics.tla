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
  /\ LET p == ContainRelInv(n) IN
      \/ /\ CatN[p] = Process
         /\ nodemarks[p] = 0  \* XXXX No multi-instance XXXX
         /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1, ![p] = @ + 1 ]
      \/ /\ CatN[p] = SubProcess
         /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ - 1 ]
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

terminateend_start(n) == \* Terminate End Event clears all token in the process/subprocess (except for the n node).
  /\ CatN[n] = TerminateEndEvent
  /\ nodemarks[n] = 0
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
  /\ Network!unchanged

(* ---- message end event ---- *)

messageend_start(n) ==
  /\ CatN[n] = MessageEndEvent
  /\ \E e1 \in intype(SeqFlowType, n), e2 \in outtype(MsgFlowType, n) :
     /\ edgemarks[e1] >= 1
     /\ Network!send(ProcessOf(n), ProcessOf(target[e2]), msgtype[e2])
     /\ edgemarks' = [ edgemarks EXCEPT ![e1] = @ - 1, ![e2] = @ + 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = 1 ]

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
      /\ UNCHANGED nodemarks

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

----------------------------------------------------------------

(* ---- Exclusive Or / XOR ---- *)

LOCAL xor_complete_out(n,eout) ==
  /\ \E ein \in intype(SeqFlowType, n) :
       /\ edgemarks[ein] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged

xor_complete(n) ==
  /\ CatN[n] = ExclusiveOr
  /\ \E eout \in outtype(SeqFlowType, n) : \* eout may be Conditional or Default
         xor_complete_out(n, eout)

LOCAL xor_fairness(n) ==
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
        /\ Network!unchanged

or_complete(n) ==
  /\ CatN[n] = InclusiveOr
  /\ \/ \E eouts \in SUBSET outtype({ NormalSeqFlow, ConditionalSeqFlow }, n) : or_complete_outs(n, eouts)
     \/ \E eout \in outtype({ DefaultSeqFlow }, n) : or_complete_outs(n, {eout})

LOCAL or_fairness(n) == \* do we need fairness on DefaultSeqFlow?
     \A eouts \in SUBSET outtype({ NormalSeqFlow, ConditionalSeqFlow }, n) : SF_var(or_complete_outs(n, eouts))

(* ---- Event Based / EXOR ---- *)

LOCAL eventbased_complete_out(n, eout) ==
  /\ \E ein \in intype(SeqFlowType, n) :
      /\ edgemarks[ein] >= 1
      /\ \E emsg \in intype(MsgFlowType, target[eout]) : edgemarks[emsg] # 0
      /\ edgemarks' = [ edgemarks EXCEPT ![ein] = @ - 1, ![eout] = @ + 1 ]
  /\ UNCHANGED nodemarks
  /\ Network!unchanged

eventbased_complete(n) ==
  /\ CatN[n] = EventBasedGateway
  /\ \E eout \in outtype(SeqFlowType, n) : eventbased_complete_out(n, eout)

LOCAL eventbased_fairness(n) ==
   \A eout \in outtype(SeqFlowType, n) : SF_var(eventbased_complete_out(n,eout))

----------------------------------------------------------------

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
  /\ \E e \in intype(SeqFlowType, n) :
       /\ edgemarks[e] >= 1
       /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nodemarks EXCEPT ![n] = @ + 1 ]
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

(* ---- SubProcess ---- *)

subprocess_start(n) ==
  /\ CatN[n] = SubProcess
  /\ \E e \in intype(SeqFlowType, n) :
     /\ edgemarks[e] >= 1
     /\ edgemarks' = [ edgemarks EXCEPT ![e] = @ - 1 ]
  /\ nodemarks' = [ nn \in DOMAIN nodemarks |->
                       IF nn = n THEN nodemarks[nn] + 1
                       ELSE IF nn \in ContainRel[n] /\ CatN[nn] \in StartEventType THEN nodemarks[nn] + 1
                       ELSE nodemarks[nn] ]
  /\ Network!unchanged

subprocess_complete(n) == 
  /\ CatN[n] = SubProcess
  /\ nodemarks[n] >= 1
  /\ \A e \in Edge : source[e] \in ContainRel[n] /\ target[e] \in ContainRel[n] => edgemarks[e] = 0
  /\ \E ee \in ContainRel[n] :
      /\ CatN[ee] \in EndEventType
      /\ nodemarks[ee] >= 1
      /\ \A x \in ContainRel[n] : x # ee => nodemarks[x] = 0
      /\ nodemarks' = [ nodemarks EXCEPT ![n] = 0, ![ee] = 0 ]
  /\ edgemarks' = [ e \in DOMAIN edgemarks |->
                      IF e \in outtype(SeqFlowType, n) THEN edgemarks[e] + 1
                      ELSE edgemarks[e] ]
  /\ Network!unchanged

(* ---- Top level Process ---- *)

process_complete(n) ==
  /\ CatN[n] = Process
  /\ nodemarks[n] = 1
  /\ \A e \in Edge : source[e] \in ContainRel[n] /\ target[e] \in ContainRel[n] => edgemarks[e] = 0
  /\ \E ee \in ContainRel[n] :
      /\ CatN[ee] \in EndEventType
      /\ nodemarks[ee] = 1
      /\ \A x \in ContainRel[n] : x # ee => nodemarks[x] = 0
      /\ nodemarks' = [ nodemarks EXCEPT ![n] = 0, ![ee] = 0 ]
  /\ UNCHANGED edgemarks
  /\ Network!unchanged

----------------------------------------------------------------

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
        \* \/ (\A n \in Node : nodemarks[n] = 0) /\ (\A n \in Edge : edgemarks[n] = 0) /\ UNCHANGED var
        \* Would be to avoid deadlock when done. But deadlock occurs too often and is
        \* catched by unsoundness => it seems better to disable deadlock detection in TLC.

Init ==
  /\ nodemarks = [ n \in Node |->
                     IF CatN[n] = NoneStartEvent /\ (\E p \in Processes : n \in ContainRel[p]) THEN 1
                     ELSE 0 ]
  /\ edgemarks = [ e \in Edge |-> 0 ]
  /\ Network!init

(* Fairness == WF_var(Next) *)
Fairness ==
  /\ \A n \in Node : WF_var(step(n))
  /\ \A n \in Node : CatN[n] = ExclusiveOr => xor_fairness(n)
  /\ \A n \in Node : CatN[n] = EventBasedGateway => eventbased_fairness(n)
  /\ \A n \in Node : CatN[n] = InclusiveOr => or_fairness(n)

Spec == Init /\ [][Next]_var /\ Fairness

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

(* When all processes have ended, there are no messages left in transit. *)
NoUndeliveredMessages ==
  []((\A p \in Processes : nodemarks[p] = 0) => (\A e \in Edge : CatE[e] = MsgFlow => edgemarks[e] = 0))

(* ---------------------------------------------------------------- *)

(* Correctness properties from F. Corradini, C. Muzi, B. Re, and F. Tiezzi, « A Classification of BPMN Collaborations based on Safeness and Soundness Notions », EXPRESS/SOS’18. *)
(* They have been adapted to our marking, where both edges and nodes hold tokens. *)

(* No sequence flow edge has more than one token. *)
SafeCollaboration ==
   [](\A e \in Edge : CatE[e] \in SeqFlowType => edgemarks[e] <= 1)

(* Either all end events are marked and there are no token anywhere else, or no tokens are left anywhere at all. *)
\* sould we include MessageEndEvent?
SoundCollaboration ==
   <>(/\ \A e \in Edge : edgemarks[e] = 0
      /\ \/ \A n \in Node : nodemarks[n] = IF CatN[n] \in {NoneEndEvent} THEN 1 ELSE 0
         \/ \A n \in Node : nodemarks[n] = 0)

(* Like SoundCollaboration, but ignore messages in transit. *)
MessageRelaxedSoundCollaboration ==
   <>(/\ \A e \in Edge : CatE[e] \in SeqFlowType => edgemarks[e] = 0
      /\ \/ \A n \in Node : nodemarks[n] = IF CatN[n] \in {NoneEndEvent} THEN 1 ELSE 0
         \/ \A n \in Node : nodemarks[n] = 0)

================================================================
