---------------------------- MODULE NetworkInbox ----------------------------
(* Fifo n-1: each process/pool has a fifo input box where senders put their messages. *)

\* CONSTANT Node, Message

LOCAL INSTANCE Sequences

VARIABLES net

TypeInvariant ==
  /\ TRUE
  \* /\ net \in [ Pool -> Seq(Pool \X Message) ]

init == net = [ x \in {} |-> <<>>]

send(from, to, m) ==
  /\ net' = IF to \in (DOMAIN net) THEN
               [ net EXCEPT ![to] = Append(@, <<from,m>>) ]
            ELSE
               [ i \in (DOMAIN net) \union {to}
                     |-> IF i = to THEN << <<from,m>> >> ELSE net[i] ]
                                 

receive(from, to, m) ==
  /\ to \in DOMAIN net
  /\ <<from,m>> = Head(net[to])
  /\ net' = [ net EXCEPT ![to] = Tail(@) ]

unchanged == UNCHANGED net

=============================================================================
