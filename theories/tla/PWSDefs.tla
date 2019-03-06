---------------- MODULE PWSDefs ----------------
EXTENDS PWSTypes

CONSTANT Node, Edge, Message, CatN, CatE, msgtype, ContainRel (* = R *), PreEdges, PreNodes

(* R^{-1}(n). Unused *)
ContainRelInv(n) == CHOOSE p \in { nn \in Node : CatN[nn] \in {Process, SubProcess} } : n \in ContainRel[p]

(* Reflexive closure of ContainRel *)
(* ContainRel[p] is the set of nodes directly in process p. *)
(* ContainRelStar[p] is the recursive inclusion relation, including the nodes of the subprocesses of p. *)
ContainRelStar(p) ==
  LET AllNodes[q \in Node] == ContainRel[q] \union UNION { AllNodes[sp] : sp \in { n \in Node : n \in ContainRel[q] /\ CatN[n] = SubProcess } }
  IN AllNodes[p]  

Processes == { n \in Node : CatN[n] = Process }

ProcessOf(n) == CHOOSE p \in Node : CatN[p] = Process /\ n \in ContainRelStar(p)

TypeAssume == /\ Edge \subseteq Node \X Node
              /\ CatN \in [ Node -> NodeType ]
              /\ CatE \in [ Edge -> EdgeType ]
              /\ msgtype \in [ Node -> SUBSET Message ]
              /\ ContainRel \in [ { n \in Node : CatN[n] \in {Process,SubProcess} } -> SUBSET Node ]

source(e) == e[1]
target(e) == e[2]

incoming(n) == { e \in Edge : target(e) = n }
outgoing(n) == { e \in Edge : source(e) = n }

succs(n) == { s \in Node : <<n,s>> \in Edge }
preds(n) == { p \in Node : <<p,n>> \in Edge }

intype(type,n)  == { e \in incoming(n) : CatE[e] \in type }
outtype(type,n) == { e \in outgoing(n) : CatE[e] \in type }


================================================================
