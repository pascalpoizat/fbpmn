---------------------------- MODULE NetworkOutbox ----------------------------
(* Fifo 1-n: each process/pool has a fifo output box where it puts outgoing messages.
   Receivers fetch from the box. *)

\* CONSTANT Node, Message

LOCAL INSTANCE Sequences

VARIABLES net

TypeInvariant ==
  /\ TRUE
  \* /\ net \in [ Pool -> Seq(Pool \X Message) ]

init == net = [ x \in {} |-> <<>>]

send(from, to, m) ==
  /\ net' = IF from \in (DOMAIN net) THEN
               [ net EXCEPT ![from] = Append(@, <<to,m>>) ]
            ELSE
               [ i \in (DOMAIN net) \union {from}
                     |-> IF i = from THEN << <<to,m>> >> ELSE net[i] ]
                                 

receive(from, to, m) ==
  /\ from \in DOMAIN net
  /\ <<to,m>> = Head(net[from])
  /\ net' = [ net EXCEPT ![from] = Tail(@) ]

unchanged == UNCHANGED net

=============================================================================
