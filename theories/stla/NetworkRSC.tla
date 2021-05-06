---------------- MODULE NetworkRSC ----------------
(* RSC - realizable with synchronous communication.
   A unique place => at most one message in transit. *)

\* CONSTANT Node, Message

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

VARIABLES net

TypeInvariant ==
  /\ Cardinality(net) <= 1

init == net = {}

send(from, to, m) ==
  /\ net = {}
  /\ net' = {<<from, to, m>>}

receive(from, to, m) ==
  /\ {<<from, to, m>>} = net
  /\ net' = {}

unchanged == UNCHANGED net

================================================================
