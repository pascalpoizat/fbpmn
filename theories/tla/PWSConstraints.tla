---------------- MODULE PWSConstraints ----------------
(* This module provides generic constraints to handle divergent models or to
   limit the state space.
   By default, no constraints are applied.
   In the cfg file, one can add overides:
   CONSTANT ConstraintNode <- MaxNodeMarking3
            ConstraintEdge <- MaxEdgeMarking2  -- or MaxMessageEdgeMarking2
            Constraint <- ConstraintNodeEdge   -- default conjunction

   More generally, Constraint may be any predicate defined in the model.
*)

EXTENDS Naturals, PWSTypes

CONSTANT ConstraintNode, ConstraintEdge,      \* TRUE = none
         Node, Edge, Message, CatN, CatE, msgtype

VARIABLES
  edgemarks,
  nodemarks

LOCAL ConstraintNodeMarking(S,c) == (c = 0) \/ (\A i \in S : nodemarks[i] <= c)
LOCAL ConstraintEdgeMarking(S,c) == (c = 0) \/ (\A i \in S : edgemarks[i] <= c)

(* Populate some constants for definition overide in cfg file. *)

MaxEdgeMarking1 == ConstraintEdgeMarking(Edge,1)
MaxEdgeMarking2 == ConstraintEdgeMarking(Edge,2)
MaxEdgeMarking3 == ConstraintEdgeMarking(Edge,3)

MaxMessageEdgeMarking1 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in MessageFlowType}, 1)
MaxMessageEdgeMarking2 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in MessageFlowType}, 2)
MaxMessageEdgeMarking3 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in MessageFlowType}, 3)

MaxSequenceEdgeMarking1 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in SeqFlowType}, 1)
MaxSequenceEdgeMarking2 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in SeqFlowType}, 2)
MaxSequenceEdgeMarking3 == ConstraintEdgeMarking({e \in Edge : CatE[e] \in SeqFlowType}, 3)

MaxNodeMarking1 == ConstraintNodeMarking(Node,1)
MaxNodeMarking2 == ConstraintNodeMarking(Node,2)
MaxNodeMarking3 == ConstraintNodeMarking(Node,3)

ConstraintNodeEdge == ConstraintNode /\ ConstraintEdge

================================================================
