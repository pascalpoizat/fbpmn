---------------- MODULE NetworkBag ----------------
\* CONSTANT Node, Message

LOCAL INSTANCE Bags

VARIABLES net

TypeInvariant ==
  /\ IsABag(net)
  \* /\ BagToSet(net) \in SUBSET Node \X Node \X Message

init == net = EmptyBag

send(from, to, m) ==
  /\ net' = net (+) SetToBag({<<from, to, m>>})

receive(from, to, m) ==
  /\ BagIn(<<from, to, m>>, net)
  /\ net' = net (-) SetToBag({<<from, to, m>>})

unchanged == UNCHANGED net

================================================================
