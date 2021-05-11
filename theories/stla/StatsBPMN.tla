---------------- MODULE StatsBPMN ----------------

EXTENDS TLC, FiniteSets

VARIABLES nodemarks, edgemarks, net
vars == <<nodemarks, edgemarks, net>>

M == INSTANCE 003OrTest

ASSUME PrintT(<< "Processes=", Cardinality({n \in M!Node : M!CatN[n] = M!Process}),
                 "Nodes=", Cardinality(M!Node),
                 "Gateway=", Cardinality({n \in M!Node : M!CatN[n] \in M!GatewayType}),
                 "SF=", Cardinality({e \in M!Edge : M!CatE[e] \in M!SeqFlowType}),
                 "MF=", Cardinality({e \in M!Edge : M!CatE[e] \in M!MessageFlowType})
              >>)

Spec == M!Init /\ [][UNCHANGED vars]_vars

================================================================
