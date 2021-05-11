---------------- MODULE e013OrSize2x3 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "A_" :> {  }

ContainRel ==
  "A_" :> { "StartEvent_1", "ExclusiveGateway_15k9ix7", "ExclusiveGateway_1ovxz2d", "ExclusiveGateway_1dofiof", "ExclusiveGateway_1v72kao", "Task_1xwy18n", "Task_1b973ma", "Task_1bno414", "Task_1jvjnjm", "ExclusiveGateway_0wbb4kr", "ExclusiveGateway_01rg1yx", "ExclusiveGateway_1d1alzz", "ExclusiveGateway_1b6y90k", "EndEvent_0reyumw", "Task_1o166o0", "Task_0h7uj4l" }

Node == { "A_", "StartEvent_1", "ExclusiveGateway_15k9ix7", "ExclusiveGateway_1ovxz2d", "ExclusiveGateway_1dofiof", "ExclusiveGateway_1v72kao", "Task_1xwy18n", "Task_1b973ma", "Task_1bno414", "Task_1jvjnjm", "ExclusiveGateway_0wbb4kr", "ExclusiveGateway_01rg1yx", "ExclusiveGateway_1d1alzz", "ExclusiveGateway_1b6y90k", "EndEvent_0reyumw", "Task_1o166o0", "Task_0h7uj4l" }

Edge == { "SequenceFlow_0n91hmc", "SequenceFlow_00e481v", "SequenceFlow_0h7fy2d", "SequenceFlow_0xd1ing", "SequenceFlow_1djolfc", "SequenceFlow_0c3vv21", "SequenceFlow_01dq60h", "SequenceFlow_0rj7tua", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1bofvkk", "SequenceFlow_1wcsu5r", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_1c7k30y", "SequenceFlow_1fvzdhj", "SequenceFlow_1kepz08", "SequenceFlow_0ql8p1h", "SequenceFlow_05ly3hz", "SequenceFlow_0z7crkn", "SequenceFlow_1si0iqd" }

Message == {  }

msgtype ==
  [ i \in {} |-> {}]


source ==
   "SequenceFlow_0n91hmc" :> "StartEvent_1"
@@ "SequenceFlow_00e481v" :> "ExclusiveGateway_15k9ix7"
@@ "SequenceFlow_0h7fy2d" :> "ExclusiveGateway_1ovxz2d"
@@ "SequenceFlow_0xd1ing" :> "ExclusiveGateway_1ovxz2d"
@@ "SequenceFlow_1djolfc" :> "ExclusiveGateway_1dofiof"
@@ "SequenceFlow_0c3vv21" :> "ExclusiveGateway_1v72kao"
@@ "SequenceFlow_01dq60h" :> "ExclusiveGateway_1dofiof"
@@ "SequenceFlow_0rj7tua" :> "ExclusiveGateway_1v72kao"
@@ "SequenceFlow_14bv8dd" :> "Task_1b973ma"
@@ "SequenceFlow_17yc9hp" :> "Task_1bno414"
@@ "SequenceFlow_1bofvkk" :> "Task_1xwy18n"
@@ "SequenceFlow_1wcsu5r" :> "Task_1jvjnjm"
@@ "SequenceFlow_0mxxo9x" :> "ExclusiveGateway_01rg1yx"
@@ "SequenceFlow_0n88gkx" :> "ExclusiveGateway_0wbb4kr"
@@ "SequenceFlow_1c7k30y" :> "ExclusiveGateway_1d1alzz"
@@ "SequenceFlow_1fvzdhj" :> "ExclusiveGateway_1b6y90k"
@@ "SequenceFlow_1kepz08" :> "ExclusiveGateway_1b6y90k"
@@ "SequenceFlow_0ql8p1h" :> "ExclusiveGateway_1dofiof"
@@ "SequenceFlow_05ly3hz" :> "Task_1o166o0"
@@ "SequenceFlow_0z7crkn" :> "ExclusiveGateway_1v72kao"
@@ "SequenceFlow_1si0iqd" :> "Task_0h7uj4l"

target ==
   "SequenceFlow_0n91hmc" :> "ExclusiveGateway_15k9ix7"
@@ "SequenceFlow_00e481v" :> "ExclusiveGateway_1ovxz2d"
@@ "SequenceFlow_0h7fy2d" :> "ExclusiveGateway_1dofiof"
@@ "SequenceFlow_0xd1ing" :> "ExclusiveGateway_1v72kao"
@@ "SequenceFlow_1djolfc" :> "Task_1bno414"
@@ "SequenceFlow_0c3vv21" :> "Task_1xwy18n"
@@ "SequenceFlow_01dq60h" :> "Task_1b973ma"
@@ "SequenceFlow_0rj7tua" :> "Task_1jvjnjm"
@@ "SequenceFlow_14bv8dd" :> "ExclusiveGateway_0wbb4kr"
@@ "SequenceFlow_17yc9hp" :> "ExclusiveGateway_0wbb4kr"
@@ "SequenceFlow_1bofvkk" :> "ExclusiveGateway_01rg1yx"
@@ "SequenceFlow_1wcsu5r" :> "ExclusiveGateway_01rg1yx"
@@ "SequenceFlow_0mxxo9x" :> "ExclusiveGateway_1d1alzz"
@@ "SequenceFlow_0n88gkx" :> "ExclusiveGateway_1d1alzz"
@@ "SequenceFlow_1c7k30y" :> "ExclusiveGateway_1b6y90k"
@@ "SequenceFlow_1fvzdhj" :> "ExclusiveGateway_15k9ix7"
@@ "SequenceFlow_1kepz08" :> "EndEvent_0reyumw"
@@ "SequenceFlow_0ql8p1h" :> "Task_1o166o0"
@@ "SequenceFlow_05ly3hz" :> "ExclusiveGateway_0wbb4kr"
@@ "SequenceFlow_0z7crkn" :> "Task_0h7uj4l"
@@ "SequenceFlow_1si0iqd" :> "ExclusiveGateway_01rg1yx"

CatN ==
   "A_" :> Process
@@ "StartEvent_1" :> NoneStartEvent
@@ "ExclusiveGateway_15k9ix7" :> ExclusiveOr
@@ "ExclusiveGateway_1ovxz2d" :> Parallel
@@ "ExclusiveGateway_1dofiof" :> InclusiveOr
@@ "ExclusiveGateway_1v72kao" :> InclusiveOr
@@ "Task_1xwy18n" :> AbstractTask
@@ "Task_1b973ma" :> AbstractTask
@@ "Task_1bno414" :> AbstractTask
@@ "Task_1jvjnjm" :> AbstractTask
@@ "ExclusiveGateway_0wbb4kr" :> InclusiveOr
@@ "ExclusiveGateway_01rg1yx" :> InclusiveOr
@@ "ExclusiveGateway_1d1alzz" :> Parallel
@@ "ExclusiveGateway_1b6y90k" :> ExclusiveOr
@@ "EndEvent_0reyumw" :> NoneEndEvent
@@ "Task_1o166o0" :> AbstractTask
@@ "Task_0h7uj4l" :> AbstractTask

CatE ==
   "SequenceFlow_0n91hmc" :> NormalSeqFlow
@@ "SequenceFlow_00e481v" :> NormalSeqFlow
@@ "SequenceFlow_0h7fy2d" :> NormalSeqFlow
@@ "SequenceFlow_0xd1ing" :> NormalSeqFlow
@@ "SequenceFlow_1djolfc" :> ConditionalSeqFlow
@@ "SequenceFlow_0c3vv21" :> DefaultSeqFlow
@@ "SequenceFlow_01dq60h" :> DefaultSeqFlow
@@ "SequenceFlow_0rj7tua" :> ConditionalSeqFlow
@@ "SequenceFlow_14bv8dd" :> NormalSeqFlow
@@ "SequenceFlow_17yc9hp" :> NormalSeqFlow
@@ "SequenceFlow_1bofvkk" :> NormalSeqFlow
@@ "SequenceFlow_1wcsu5r" :> NormalSeqFlow
@@ "SequenceFlow_0mxxo9x" :> NormalSeqFlow
@@ "SequenceFlow_0n88gkx" :> NormalSeqFlow
@@ "SequenceFlow_1c7k30y" :> NormalSeqFlow
@@ "SequenceFlow_1fvzdhj" :> ConditionalSeqFlow
@@ "SequenceFlow_1kepz08" :> DefaultSeqFlow
@@ "SequenceFlow_0ql8p1h" :> ConditionalSeqFlow
@@ "SequenceFlow_05ly3hz" :> NormalSeqFlow
@@ "SequenceFlow_0z7crkn" :> ConditionalSeqFlow
@@ "SequenceFlow_1si0iqd" :> NormalSeqFlow

LOCAL preEdges ==
   <<"ExclusiveGateway_1dofiof", "SequenceFlow_0h7fy2d">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_05ly3hz", "SequenceFlow_0c3vv21", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0rj7tua", "SequenceFlow_0xd1ing", "SequenceFlow_0z7crkn", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1bofvkk", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj", "SequenceFlow_1si0iqd", "SequenceFlow_1wcsu5r"}
@@ <<"ExclusiveGateway_1v72kao", "SequenceFlow_0xd1ing">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_05ly3hz", "SequenceFlow_0c3vv21", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0rj7tua", "SequenceFlow_0z7crkn", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1bofvkk", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj", "SequenceFlow_1si0iqd", "SequenceFlow_1wcsu5r"}
@@ <<"ExclusiveGateway_0wbb4kr", "SequenceFlow_14bv8dd">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_0c3vv21", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0rj7tua", "SequenceFlow_0xd1ing", "SequenceFlow_0z7crkn", "SequenceFlow_1bofvkk", "SequenceFlow_1c7k30y", "SequenceFlow_1fvzdhj", "SequenceFlow_1si0iqd", "SequenceFlow_1wcsu5r"}
@@ <<"ExclusiveGateway_0wbb4kr", "SequenceFlow_17yc9hp">> :> {"SequenceFlow_00e481v", "SequenceFlow_0c3vv21", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0rj7tua", "SequenceFlow_0xd1ing", "SequenceFlow_0z7crkn", "SequenceFlow_1bofvkk", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj", "SequenceFlow_1si0iqd", "SequenceFlow_1wcsu5r"}
@@ <<"ExclusiveGateway_0wbb4kr", "SequenceFlow_05ly3hz">> :> {"SequenceFlow_00e481v", "SequenceFlow_0c3vv21", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0rj7tua", "SequenceFlow_0xd1ing", "SequenceFlow_0z7crkn", "SequenceFlow_1bofvkk", "SequenceFlow_1c7k30y", "SequenceFlow_1fvzdhj", "SequenceFlow_1si0iqd", "SequenceFlow_1wcsu5r"}
@@ <<"ExclusiveGateway_01rg1yx", "SequenceFlow_1bofvkk">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_05ly3hz", "SequenceFlow_0c3vv21", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0xd1ing", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj"}
@@ <<"ExclusiveGateway_01rg1yx", "SequenceFlow_1wcsu5r">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_05ly3hz", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0rj7tua", "SequenceFlow_0xd1ing", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj"}
@@ <<"ExclusiveGateway_01rg1yx", "SequenceFlow_1si0iqd">> :> {"SequenceFlow_00e481v", "SequenceFlow_01dq60h", "SequenceFlow_05ly3hz", "SequenceFlow_0h7fy2d", "SequenceFlow_0mxxo9x", "SequenceFlow_0n88gkx", "SequenceFlow_0n91hmc", "SequenceFlow_0ql8p1h", "SequenceFlow_0xd1ing", "SequenceFlow_0z7crkn", "SequenceFlow_14bv8dd", "SequenceFlow_17yc9hp", "SequenceFlow_1c7k30y", "SequenceFlow_1djolfc", "SequenceFlow_1fvzdhj"}
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

