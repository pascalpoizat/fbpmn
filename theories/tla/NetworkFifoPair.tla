---------------------------- MODULE NetworkFifoPair ----------------------------
(* Fifo 1-1: a queue between each couple of processes/pools. *)

\* CONSTANT Node, Message

LOCAL INSTANCE Sequences

VARIABLES net

TypeInvariant ==
  /\ TRUE
  \* /\ net \in [ (Pool \X Pool) -> Seq(Message) ]

init == net = [ x \in {} |-> <<>>]

send(from, to, m) ==
  /\ net' = IF <<from,to>> \in (DOMAIN net) THEN
               [ net EXCEPT ![from,to] = Append(@, m) ]
            ELSE
               [ <<i,j>> \in (DOMAIN net) \union {<<from,to>>}
                     |-> IF <<i,j>> = <<from,to>> THEN <<m>> ELSE net[i,j] ]
                                 

receive(from, to, m) ==
  /\ <<from,to>> \in DOMAIN net
  /\ m = Head(net[from,to])
  /\ net' = [ net EXCEPT ![from,to] = Tail(@) ]

unchanged == UNCHANGED net

=============================================================================
