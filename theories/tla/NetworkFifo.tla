---------------------------- MODULE NetworkFifo ----------------------------
(* Fifo n-n: a global unique queue. *)

\* CONSTANT Node, Message

LOCAL INSTANCE Sequences

VARIABLES net

TypeInvariant ==
  /\ TRUE
  \* /\ net \in Seq(Pool \X Pool \X Message)

init == net = <<>>

send(from, to, m) ==
  /\ net' = Append(net, <<from, to, m >>)

receive(from, to, m) ==
  /\ net /= <<>>
  /\ <<from, to, m>> = Head(net)
  /\ net' = Tail(net)

unchanged == UNCHANGED net

=============================================================================
