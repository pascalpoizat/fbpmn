---------------- MODULE PWSDefs ----------------
EXTENDS PWSTypes

CONSTANT Node, Edge, Message
CONSTANT source, target, CatN, CatE, msgtype, ContainRel (* = R *)
CONSTANT PreEdges(_,_), PreNodes(_,_), BoundaryEvent, Interest

(* space BPMN *)
CONSTANT Var, BaseLocation, GroupLocation, Location, SpaceEdge, CodeCondition
CONSTANT SpaceSource, SpaceTarget, startsub, startloc, varloc, cVar, cKind, cCond, aKind, aCond, aUpdateVar, aUpdateGPlus, aUpdateGMinus
CONSTANT locvar, evalF(_,_,_,_), order(_,_)
(* end space BPMN *)

(* R^{-1}(n). *)
ContainRelInv(n) == CHOOSE p \in { nn \in Node : CatN[nn] \in {Process, SubProcess} } : n \in ContainRel[p]

(* Transitive closure of ContainRel *)
(* ContainRel[p] is the set of nodes directly in p. *)
(* ContainRelPlus[p] is the recursive inclusion relation, including the nodes of the subprocesses of p. *)
ContainRelPlus(p) ==
  LET AllNodes[q \in Node] == ContainRel[q] \union UNION { AllNodes[sp] : sp \in { n \in Node : n \in ContainRel[q] /\ CatN[n] = SubProcess } }
  IN AllNodes[p]  

Processes == { n \in Node : CatN[n] = Process }

ProcessOf(n) == CHOOSE p \in Node : CatN[p] = Process /\ n \in ContainRelPlus(p)

WellTyped == /\ source \in [ Edge -> Node ]
             /\ target \in [ Edge -> Node ]
             /\ CatN \in [ Node -> NodeType ]
             /\ CatE \in [ Edge -> EdgeType ]
             /\ msgtype \in [ { e \in Edge : CatE[e] = MessageFlow } -> Message ]
             /\ ContainRel \in [ { n \in Node : CatN[n] \in {Process,SubProcess} } -> SUBSET Node ]
             \* PreEdges, PreNodes, BoundaryEvent, Interest TODO:
             (* space BPMN *)
             /\ SpaceSource \in [ SpaceEdge -> BaseLocation ]
             /\ SpaceTarget \in [ SpaceEdge -> BaseLocation ]
             /\ startsub \in [ GroupLocation -> SUBSET BaseLocation ]
             /\ startloc \in [ { n \in Node : CatN[n] \in {Process} } -> BaseLocation ]
             /\ varloc \in [ { n \in Node : CatN[n] \in {Process} }  -> Var ]
             /\ cVar \in [ { e \in Edge : CatE[e] \in {ConditionalSeqFlow} } -> Var ]
             /\ cKind \in [ { e \in Edge : CatE[e] \in {ConditionalSeqFlow} } -> {Some,All} ]
             /\ cCond \in [ { e \in Edge : CatE[e] \in {ConditionalSeqFlow} } -> CodeCondition ]
             /\ aKind \in [ { n \in Node : CatN[n] \in {AbstractTask} } -> TypeAction ]
             /\ aCond \in [{ n \in Node : CatN[n] \in {AbstractTask} /\ aKind[n] \in {ACT_MOVE} }-> CodeCondition]
             /\ aUpdateVar \in [ { n \in Node : CatN[n] \in {AbstractTask} /\ aKind[n] \in {ACT_UPDATE} } -> Var]
             /\ aUpdateGPlus \in [ { n \in Node : CatN[n] \in {AbstractTask} /\ aKind[n] \in {ACT_UPDATE} } -> SUBSET  GroupLocation]
             /\ aUpdateGMinus \in [ { n \in Node : CatN[n] \in {AbstractTask} /\ aKind[n] \in {ACT_UPDATE} } -> SUBSET  GroupLocation]
             \* locvar, evalF(_,_,_,_),  order(_,_) TODO:
             (* end space BPMN *)
     
incoming(n) == { e \in Edge : target[e] = n }
outgoing(n) == { e \in Edge : source[e] = n }

succs(n) == { target[e] : e \in outgoing(n) }
preds(n) == { source[e] : e \in incoming(n) }

intype(type,n)  == { e \in incoming(n) : CatE[e] \in type }
outtype(type,n) == { e \in outgoing(n) : CatE[e] \in type }

UnchangedSigma(v) == v' = v \* FIXME: use UNCHANGED

UnchangedSubs(s) == s' = s \* FIXME: use UNCHANGED

UnchangedSpace(v,s) == /\ UnchangedSigma(v) \* FIXME: use UNCHANGED
                       /\ UnchangedSubs(s) \* FIXME: use UNCHANGED

(* v1 *)
(*
evalMove(n,v,s) ==  /\ UnchangedSubs(s)
                    /\ LET newPos == evalF(v,s,ProcessOf(n), aCond[n]) IN 
                          IF newPos#{} THEN v' = [v EXCEPT ![varloc[ProcessOf(n)]] = {CHOOSE x \in newPos : TRUE }] 
                           ELSE UnchangedSigma(v)
*)
    
(* v2 *)
evalMove(n,v,s) ==  /\ UnchangedSubs(s)
                    /\ LET newPos == evalF(v,s,ProcessOf(n), aCond[n]) IN 
                            \E x \in newPos :  v' = [v EXCEPT ![varloc[ProcessOf(n)]] = {x}] 

evalUpdate(n,v,s) == /\ UnchangedSigma(v)
                    /\ s' = [x \in GroupLocation |-> 
                    IF (x \in aUpdateGMinus[n]) THEN s[x]\v[aUpdateVar[n]]
                    ELSE IF (x \in aUpdateGPlus[n]) THEN UNION{ s[x] \union v[aUpdateVar[n]]}
                    ELSE s[x]]
              
evalAction(n,v,s) ==  IF aKind[n] = ACT_MOVE THEN evalMove(n,v,s)
                      ELSE IF aKind[n] = ACT_UPDATE THEN evalUpdate(n,v,s)
                      ELSE UnchangedSpace(v,s)

================================================================
