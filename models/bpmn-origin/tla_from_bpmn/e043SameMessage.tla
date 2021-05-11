---------------- MODULE e043SameMessage ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Pid" :> { "Info" }
  @@ "Qid" :> { "Info" }

ContainRel ==
  "Pid" :> { "StartEvent_1", "Task_1640yub", "Task_1yxycrc", "EndEvent_15dkjc7", "Task_125lbbu", "Task_0rim1ab" }
  @@ "Qid" :> { "StartEvent_131stvt", "SendTask_1ukbqce", "ReceiveTask_12v7zb0", "EndEvent_0z166lz", "Task_1dr6jww", "Task_1jdqb88" }

Node == { "Pid", "Qid", "StartEvent_1", "Task_1640yub", "Task_1yxycrc", "EndEvent_15dkjc7", "Task_125lbbu", "Task_0rim1ab", "StartEvent_131stvt", "SendTask_1ukbqce", "ReceiveTask_12v7zb0", "EndEvent_0z166lz", "Task_1dr6jww", "Task_1jdqb88" }

Edge == { "MessageFlow_08078h0", "MessageFlow_0ethk5r", "MessageFlow_1sbztdc", "MessageFlow_1i8pa9a", "SequenceFlow_1e8j5gg", "SequenceFlow_0ul5cp9", "SequenceFlow_1gr5udw", "SequenceFlow_0x0ua9p", "SequenceFlow_136ue2u", "SequenceFlow_1kr124p", "SequenceFlow_1ajd21l", "SequenceFlow_1u8e5ni", "SequenceFlow_0ww2wl4", "SequenceFlow_19mve9z" }

Message == { "Info" }

msgtype ==
   "MessageFlow_08078h0" :> "Info"
@@ "MessageFlow_0ethk5r" :> "Info"
@@ "MessageFlow_1sbztdc" :> "Info"
@@ "MessageFlow_1i8pa9a" :> "Info"


source ==
   "MessageFlow_08078h0" :> "Task_1640yub"
@@ "MessageFlow_0ethk5r" :> "ReceiveTask_12v7zb0"
@@ "MessageFlow_1sbztdc" :> "Task_125lbbu"
@@ "MessageFlow_1i8pa9a" :> "Task_1jdqb88"
@@ "SequenceFlow_1e8j5gg" :> "StartEvent_1"
@@ "SequenceFlow_0ul5cp9" :> "Task_1640yub"
@@ "SequenceFlow_1gr5udw" :> "Task_1yxycrc"
@@ "SequenceFlow_0x0ua9p" :> "Task_125lbbu"
@@ "SequenceFlow_136ue2u" :> "Task_0rim1ab"
@@ "SequenceFlow_1kr124p" :> "StartEvent_131stvt"
@@ "SequenceFlow_1ajd21l" :> "SendTask_1ukbqce"
@@ "SequenceFlow_1u8e5ni" :> "ReceiveTask_12v7zb0"
@@ "SequenceFlow_0ww2wl4" :> "Task_1dr6jww"
@@ "SequenceFlow_19mve9z" :> "Task_1jdqb88"

target ==
   "MessageFlow_08078h0" :> "SendTask_1ukbqce"
@@ "MessageFlow_0ethk5r" :> "Task_1yxycrc"
@@ "MessageFlow_1sbztdc" :> "Task_1dr6jww"
@@ "MessageFlow_1i8pa9a" :> "Task_0rim1ab"
@@ "SequenceFlow_1e8j5gg" :> "Task_1640yub"
@@ "SequenceFlow_0ul5cp9" :> "Task_1yxycrc"
@@ "SequenceFlow_1gr5udw" :> "Task_125lbbu"
@@ "SequenceFlow_0x0ua9p" :> "Task_0rim1ab"
@@ "SequenceFlow_136ue2u" :> "EndEvent_15dkjc7"
@@ "SequenceFlow_1kr124p" :> "SendTask_1ukbqce"
@@ "SequenceFlow_1ajd21l" :> "ReceiveTask_12v7zb0"
@@ "SequenceFlow_1u8e5ni" :> "Task_1dr6jww"
@@ "SequenceFlow_0ww2wl4" :> "Task_1jdqb88"
@@ "SequenceFlow_19mve9z" :> "EndEvent_0z166lz"

CatN ==
   "Pid" :> Process
@@ "Qid" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "Task_1640yub" :> SendTask
@@ "Task_1yxycrc" :> ReceiveTask
@@ "EndEvent_15dkjc7" :> NoneEndEvent
@@ "Task_125lbbu" :> SendTask
@@ "Task_0rim1ab" :> ReceiveTask
@@ "StartEvent_131stvt" :> NoneStartEvent
@@ "SendTask_1ukbqce" :> ReceiveTask
@@ "ReceiveTask_12v7zb0" :> SendTask
@@ "EndEvent_0z166lz" :> NoneEndEvent
@@ "Task_1dr6jww" :> ReceiveTask
@@ "Task_1jdqb88" :> SendTask

CatE ==
   "MessageFlow_08078h0" :> MessageFlow
@@ "MessageFlow_0ethk5r" :> MessageFlow
@@ "MessageFlow_1sbztdc" :> MessageFlow
@@ "MessageFlow_1i8pa9a" :> MessageFlow
@@ "SequenceFlow_1e8j5gg" :> NormalSeqFlow
@@ "SequenceFlow_0ul5cp9" :> NormalSeqFlow
@@ "SequenceFlow_1gr5udw" :> NormalSeqFlow
@@ "SequenceFlow_0x0ua9p" :> NormalSeqFlow
@@ "SequenceFlow_136ue2u" :> NormalSeqFlow
@@ "SequenceFlow_1kr124p" :> NormalSeqFlow
@@ "SequenceFlow_1ajd21l" :> NormalSeqFlow
@@ "SequenceFlow_1u8e5ni" :> NormalSeqFlow
@@ "SequenceFlow_0ww2wl4" :> NormalSeqFlow
@@ "SequenceFlow_19mve9z" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
  [ i \in {} |-> {}]

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

