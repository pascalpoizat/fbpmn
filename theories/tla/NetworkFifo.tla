---------------------------- MODULE NetworkFifo ----------------------------
\* CONSTANT Node, Message

LOCAL INSTANCE Sequences

VARIABLES net

TypeInvariant ==
  /\ TRUE
  \* /\ net \in Seq(Node \X Node \X Message)

init == net = <<>>

send(from, to, m) ==
  /\ net' = Append(net, <<from, to, m >>)

receive(from, to, m) ==
  /\ net /= <<>>
  /\ <<from, to, m>> = Head(net)
  /\ net' = Tail(net)

unchanged == UNCHANGED net

=============================================================================
