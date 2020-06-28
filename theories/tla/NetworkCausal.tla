---------------- MODULE NetworkCausal ----------------


EXTENDS Naturals
LOCAL INSTANCE Bags

CONSTANT PEERS

VARIABLES net

LOCAL Max(a, b) == IF a >= b THEN a ELSE b

TypeInvariant ==    /\ IsABag(net.bag) 

init == net = 
            [
                bag             |-> EmptyBag,
                vectorClocks    |-> [p \in PEERS |-> [ x \in PEERS |-> 0 ] ]
            ]

send(from, to, m) == LET vc == [net.vectorClocks[from] EXCEPT ![from] = @ + 1]
                     IN  net' = [net EXCEPT !.bag = @ (+) SetToBag({<<from, to, m, vc>>}),
                                            !.vectorClocks = [@ EXCEPT ![from] = vc] ]

receive(from, to, m) == \E message \in DOMAIN net.bag : 
                            /\ message[1] = from
                            /\ message[2] = to
                            /\ message[3] = m
                            /\ LET vc == message[4] IN
                                /\ \neg ( \E anotherMessage \in DOMAIN net.bag :
                                                    /\ anotherMessage[2] = to
                                                    /\ anotherMessage /= message
                                                    /\ LET vc2 == anotherMessage[4] IN (\A p \in PEERS : vc2[p] =< vc[p] ) )

                                /\ net' = [net EXCEPT !.bag = @ (-) SetToBag({<<from, to, m, vc>>}),
                                                  !.vectorClocks = [@ EXCEPT ![to] = [ p \in PEERS |-> Max(@[p], vc[p])]]]

                                

unchanged == UNCHANGED net

================================================================
