---------------- MODULE e032MBE ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "P_" :> { "m2", "m1" }
  @@ "Q_" :> {  }

ContainRel ==
  "P_" :> { "StartEvent_1", "ExclusiveGateway_1uyyba4", "Task_1rjwiou", "Task_05h2dnk", "ExclusiveGateway_04stbki", "SubProcess_0ikactq", "ExclusiveGateway_06yyw6a", "EndEvent_1bmsqno", "BoundaryEvent_1g6jly9" }
  @@ "Q_" :> { "StartEvent_0pevvbh", "EndEvent_03g8tis", "Task_1rw2ter", "Task_0dvwezg" }
  @@ "SubProcess_0ikactq" :> { "StartEvent_1em4yhi", "EndEvent_07lweo2", "Task_1kf2bvv" }

Node == { "P_", "Q_", "StartEvent_1", "ExclusiveGateway_1uyyba4", "Task_1rjwiou", "Task_05h2dnk", "ExclusiveGateway_04stbki", "SubProcess_0ikactq", "ExclusiveGateway_06yyw6a", "EndEvent_1bmsqno", "BoundaryEvent_1g6jly9", "StartEvent_1em4yhi", "EndEvent_07lweo2", "Task_1kf2bvv", "StartEvent_0pevvbh", "EndEvent_03g8tis", "Task_1rw2ter", "Task_0dvwezg" }

Edge == { "MessageFlow_1arf9uv", "MessageFlow_0zlj6zo", "SequenceFlow_1uzescv", "SequenceFlow_1qymta9", "SequenceFlow_1t3nh6y", "SequenceFlow_07f8qba", "SequenceFlow_0aq5v2x", "SequenceFlow_0ylruuw", "SequenceFlow_13u1qxz", "SequenceFlow_1wro3pq", "SequenceFlow_0fh3j7y", "SequenceFlow_1ofsg25", "SequenceFlow_0j6nnaa", "SequenceFlow_0r3bens", "SequenceFlow_1gn3q83", "SequenceFlow_0f6i1ig" }

Message == { "m1", "m2" }

msgtype ==
   "MessageFlow_1arf9uv" :> "m1"
@@ "MessageFlow_0zlj6zo" :> "m2"


source ==
   "MessageFlow_1arf9uv" :> "Task_0dvwezg"
@@ "MessageFlow_0zlj6zo" :> "Task_1rw2ter"
@@ "SequenceFlow_1uzescv" :> "StartEvent_1"
@@ "SequenceFlow_1qymta9" :> "ExclusiveGateway_1uyyba4"
@@ "SequenceFlow_1t3nh6y" :> "ExclusiveGateway_1uyyba4"
@@ "SequenceFlow_07f8qba" :> "Task_1rjwiou"
@@ "SequenceFlow_0aq5v2x" :> "Task_05h2dnk"
@@ "SequenceFlow_0ylruuw" :> "ExclusiveGateway_04stbki"
@@ "SequenceFlow_13u1qxz" :> "ExclusiveGateway_06yyw6a"
@@ "SequenceFlow_1wro3pq" :> "SubProcess_0ikactq"
@@ "SequenceFlow_0fh3j7y" :> "BoundaryEvent_1g6jly9"
@@ "SequenceFlow_1ofsg25" :> "StartEvent_1em4yhi"
@@ "SequenceFlow_0j6nnaa" :> "Task_1kf2bvv"
@@ "SequenceFlow_0r3bens" :> "StartEvent_0pevvbh"
@@ "SequenceFlow_1gn3q83" :> "Task_0dvwezg"
@@ "SequenceFlow_0f6i1ig" :> "Task_1rw2ter"

target ==
   "MessageFlow_1arf9uv" :> "Task_1kf2bvv"
@@ "MessageFlow_0zlj6zo" :> "BoundaryEvent_1g6jly9"
@@ "SequenceFlow_1uzescv" :> "ExclusiveGateway_1uyyba4"
@@ "SequenceFlow_1qymta9" :> "Task_1rjwiou"
@@ "SequenceFlow_1t3nh6y" :> "Task_05h2dnk"
@@ "SequenceFlow_07f8qba" :> "ExclusiveGateway_04stbki"
@@ "SequenceFlow_0aq5v2x" :> "ExclusiveGateway_04stbki"
@@ "SequenceFlow_0ylruuw" :> "SubProcess_0ikactq"
@@ "SequenceFlow_13u1qxz" :> "EndEvent_1bmsqno"
@@ "SequenceFlow_1wro3pq" :> "ExclusiveGateway_06yyw6a"
@@ "SequenceFlow_0fh3j7y" :> "ExclusiveGateway_06yyw6a"
@@ "SequenceFlow_1ofsg25" :> "Task_1kf2bvv"
@@ "SequenceFlow_0j6nnaa" :> "EndEvent_07lweo2"
@@ "SequenceFlow_0r3bens" :> "Task_1rw2ter"
@@ "SequenceFlow_1gn3q83" :> "EndEvent_03g8tis"
@@ "SequenceFlow_0f6i1ig" :> "Task_0dvwezg"

CatN ==
   "P_" :> Process
@@ "Q_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_1uyyba4" :> Parallel
@@ "Task_1rjwiou" :> AbstractTask
@@ "Task_05h2dnk" :> AbstractTask
@@ "ExclusiveGateway_04stbki" :> ExclusiveOr
@@ "SubProcess_0ikactq" :> SubProcess
@@ "ExclusiveGateway_06yyw6a" :> Parallel
@@ "EndEvent_1bmsqno" :> NoneEndEvent
@@ "BoundaryEvent_1g6jly9" :> MessageBoundaryEvent
@@ "StartEvent_1em4yhi" :> NoneStartEvent
@@ "EndEvent_07lweo2" :> NoneEndEvent
@@ "Task_1kf2bvv" :> ReceiveTask
@@ "StartEvent_0pevvbh" :> NoneStartEvent
@@ "EndEvent_03g8tis" :> NoneEndEvent
@@ "Task_1rw2ter" :> SendTask
@@ "Task_0dvwezg" :> SendTask

CatE ==
   "MessageFlow_1arf9uv" :> MessageFlow
@@ "MessageFlow_0zlj6zo" :> MessageFlow
@@ "SequenceFlow_1uzescv" :> NormalSeqFlow
@@ "SequenceFlow_1qymta9" :> NormalSeqFlow
@@ "SequenceFlow_1t3nh6y" :> NormalSeqFlow
@@ "SequenceFlow_07f8qba" :> NormalSeqFlow
@@ "SequenceFlow_0aq5v2x" :> NormalSeqFlow
@@ "SequenceFlow_0ylruuw" :> NormalSeqFlow
@@ "SequenceFlow_13u1qxz" :> NormalSeqFlow
@@ "SequenceFlow_1wro3pq" :> NormalSeqFlow
@@ "SequenceFlow_0fh3j7y" :> NormalSeqFlow
@@ "SequenceFlow_1ofsg25" :> NormalSeqFlow
@@ "SequenceFlow_0j6nnaa" :> NormalSeqFlow
@@ "SequenceFlow_0r3bens" :> NormalSeqFlow
@@ "SequenceFlow_1gn3q83" :> NormalSeqFlow
@@ "SequenceFlow_0f6i1ig" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "BoundaryEvent_1g6jly9" :> [ attachedTo |-> "SubProcess_0ikactq", cancelActivity |-> TRUE ]

WF == INSTANCE PWSWellFormed
ASSUME WF!WellTyped
ASSUME WF!WellFormedness

ConstraintNode == TRUE \* none
ConstraintEdge == TRUE \* none
Constraint == TRUE     \* none
INSTANCE PWSConstraints
INSTANCE UserProperties
INSTANCE PWSSemantics

================================================================

