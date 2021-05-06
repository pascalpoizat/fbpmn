---------------- MODULE e020InternshipProcedure ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Company_" :> { "agreement" }
  @@ "InternshipDelegate_" :> { "termination notification", "documentation" }
  @@ "InternshipOffice_" :> { "proposal", "access", "registration", "login" }
  @@ "Student_" :> { "internship completion" }

ContainRel ==
  "Company_" :> { "Task_1ukgtgd", "Task_0k3desy", "EndEvent_0g8hfyq", "Task_0z00tzq", "Task_1awa0vf", "Task_13r7bmt", "Task_10ik9d4", "Task_06e9es5", "Task_0zi619x", "ExclusiveGateway_1ojvmkc", "Task_16a1dy1", "Task_0ieueaf", "StartEvent_1wgj96l", "ExclusiveGateway_1wor220" }
  @@ "InternshipDelegate_" :> { "StartEvent_0sg8ueb", "SendTask_0bu2egl", "ReceiveTask_1eiaojy", "EndEvent_0r34c4w", "SendTask_1sfy3aq" }
  @@ "InternshipOffice_" :> { "IntermediateCatchEvent_180guhd", "IntermediateCatchEvent_0oxyhte", "ExclusiveGateway_025el3u", "ReceiveTask_146lfh4", "EndEvent_0zeqiic", "StartEvent_0y07koo", "EventBasedGateway_1d92ix7" }
  @@ "Student_" :> { "StartEvent_0efqept", "ExclusiveGateway_1pvytgl", "ExclusiveGateway_10r796g", "Task_05rcgao", "Task_12w7z0s", "Task_0kueqty", "Task_16mub7w", "Task_0y40xht", "EndEvent_131pwct" }

Node == { "Student_", "Company_", "InternshipOffice_", "InternshipDelegate_", "StartEvent_0efqept", "ExclusiveGateway_1pvytgl", "ExclusiveGateway_10r796g", "Task_05rcgao", "Task_12w7z0s", "Task_0kueqty", "Task_16mub7w", "Task_0y40xht", "EndEvent_131pwct", "Task_1ukgtgd", "Task_0k3desy", "EndEvent_0g8hfyq", "Task_0z00tzq", "Task_1awa0vf", "Task_13r7bmt", "Task_10ik9d4", "Task_06e9es5", "Task_0zi619x", "ExclusiveGateway_1ojvmkc", "Task_16a1dy1", "Task_0ieueaf", "StartEvent_1wgj96l", "ExclusiveGateway_1wor220", "IntermediateCatchEvent_180guhd", "IntermediateCatchEvent_0oxyhte", "ExclusiveGateway_025el3u", "ReceiveTask_146lfh4", "EndEvent_0zeqiic", "StartEvent_0y07koo", "EventBasedGateway_1d92ix7", "StartEvent_0sg8ueb", "SendTask_0bu2egl", "ReceiveTask_1eiaojy", "EndEvent_0r34c4w", "SendTask_1sfy3aq" }

Edge == { "MessageFlow_1r2202w", "MessageFlow_0vajuh0", "MessageFlow_1exti3v", "MessageFlow_0whwr08", "MessageFlow_1uu4df2", "MessageFlow_0qzpag3", "MessageFlow_0n79ikw", "MessageFlow_0n7crx1", "SequenceFlow_19jde9o", "SequenceFlow_07e105b", "SequenceFlow_1nsmz5l", "SequenceFlow_1a0w8i4", "SequenceFlow_1hv2qod", "SequenceFlow_04fa4c4", "SequenceFlow_0epxxie", "SequenceFlow_1716tm6", "SequenceFlow_1e21rh4", "SequenceFlow_0nlul5d", "SequenceFlow_0oaajbr", "SequenceFlow_1v26cki", "SequenceFlow_0bferc8", "SequenceFlow_0rqes4b", "SequenceFlow_19fg7gc", "SequenceFlow_0upqxnz", "SequenceFlow_0tbrrh9", "SequenceFlow_0ye9pwd", "SequenceFlow_007i0gb", "SequenceFlow_036yd4w", "SequenceFlow_1wxr7td", "SequenceFlow_1hrqezf", "SequenceFlow_12e7qby", "SequenceFlow_09fa10u", "SequenceFlow_0cxrm8j", "SequenceFlow_0lkr4ww", "SequenceFlow_1h50tfu", "SequenceFlow_1nxvmw1", "SequenceFlow_0f1t7q4", "SequenceFlow_1ssp09f", "SequenceFlow_07c1y6g", "SequenceFlow_0woxsim", "SequenceFlow_1ifwhto", "SequenceFlow_0ol0c8s" }

Message == { "agreement", "termination notification", "internship completion", "documentation", "login", "registration", "proposal", "access" }

msgtype ==
   "MessageFlow_1r2202w" :> "agreement"
@@ "MessageFlow_0vajuh0" :> "termination notification"
@@ "MessageFlow_1exti3v" :> "internship completion"
@@ "MessageFlow_0whwr08" :> "documentation"
@@ "MessageFlow_1uu4df2" :> "login"
@@ "MessageFlow_0qzpag3" :> "registration"
@@ "MessageFlow_0n79ikw" :> "proposal"
@@ "MessageFlow_0n7crx1" :> "access"


source ==
   "MessageFlow_1r2202w" :> "Task_0kueqty"
@@ "MessageFlow_0vajuh0" :> "Task_0z00tzq"
@@ "MessageFlow_1exti3v" :> "SendTask_0bu2egl"
@@ "MessageFlow_0whwr08" :> "Task_10ik9d4"
@@ "MessageFlow_1uu4df2" :> "Task_0k3desy"
@@ "MessageFlow_0qzpag3" :> "Task_1ukgtgd"
@@ "MessageFlow_0n79ikw" :> "Task_13r7bmt"
@@ "MessageFlow_0n7crx1" :> "Task_0ieueaf"
@@ "SequenceFlow_19jde9o" :> "Task_0y40xht"
@@ "SequenceFlow_07e105b" :> "Task_12w7z0s"
@@ "SequenceFlow_1nsmz5l" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_1a0w8i4" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_1hv2qod" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_04fa4c4" :> "Task_05rcgao"
@@ "SequenceFlow_0epxxie" :> "StartEvent_0efqept"
@@ "SequenceFlow_1716tm6" :> "Task_16mub7w"
@@ "SequenceFlow_1e21rh4" :> "Task_0kueqty"
@@ "SequenceFlow_0nlul5d" :> "Task_0z00tzq"
@@ "SequenceFlow_0oaajbr" :> "Task_1awa0vf"
@@ "SequenceFlow_1v26cki" :> "Task_16a1dy1"
@@ "SequenceFlow_0bferc8" :> "Task_10ik9d4"
@@ "SequenceFlow_0rqes4b" :> "Task_0k3desy"
@@ "SequenceFlow_19fg7gc" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_0upqxnz" :> "Task_1ukgtgd"
@@ "SequenceFlow_0tbrrh9" :> "Task_06e9es5"
@@ "SequenceFlow_0ye9pwd" :> "Task_0zi619x"
@@ "SequenceFlow_007i0gb" :> "Task_0ieueaf"
@@ "SequenceFlow_036yd4w" :> "Task_13r7bmt"
@@ "SequenceFlow_1wxr7td" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_1hrqezf" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_12e7qby" :> "StartEvent_1wgj96l"
@@ "SequenceFlow_09fa10u" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_0cxrm8j" :> "IntermediateCatchEvent_180guhd"
@@ "SequenceFlow_0lkr4ww" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_1h50tfu" :> "IntermediateCatchEvent_0oxyhte"
@@ "SequenceFlow_1nxvmw1" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_0f1t7q4" :> "ReceiveTask_146lfh4"
@@ "SequenceFlow_1ssp09f" :> "StartEvent_0y07koo"
@@ "SequenceFlow_07c1y6g" :> "StartEvent_0sg8ueb"
@@ "SequenceFlow_0woxsim" :> "SendTask_1sfy3aq"
@@ "SequenceFlow_1ifwhto" :> "ReceiveTask_1eiaojy"
@@ "SequenceFlow_0ol0c8s" :> "SendTask_0bu2egl"

target ==
   "MessageFlow_1r2202w" :> "Task_0zi619x"
@@ "MessageFlow_0vajuh0" :> "ReceiveTask_1eiaojy"
@@ "MessageFlow_1exti3v" :> "Task_0y40xht"
@@ "MessageFlow_0whwr08" :> "StartEvent_0sg8ueb"
@@ "MessageFlow_1uu4df2" :> "IntermediateCatchEvent_180guhd"
@@ "MessageFlow_0qzpag3" :> "IntermediateCatchEvent_0oxyhte"
@@ "MessageFlow_0n79ikw" :> "ReceiveTask_146lfh4"
@@ "MessageFlow_0n7crx1" :> "StartEvent_0y07koo"
@@ "SequenceFlow_19jde9o" :> "EndEvent_131pwct"
@@ "SequenceFlow_07e105b" :> "Task_0y40xht"
@@ "SequenceFlow_1nsmz5l" :> "Task_16mub7w"
@@ "SequenceFlow_1a0w8i4" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_1hv2qod" :> "Task_05rcgao"
@@ "SequenceFlow_04fa4c4" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_0epxxie" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_1716tm6" :> "Task_0kueqty"
@@ "SequenceFlow_1e21rh4" :> "Task_12w7z0s"
@@ "SequenceFlow_0nlul5d" :> "EndEvent_0g8hfyq"
@@ "SequenceFlow_0oaajbr" :> "Task_0z00tzq"
@@ "SequenceFlow_1v26cki" :> "Task_1awa0vf"
@@ "SequenceFlow_0bferc8" :> "Task_16a1dy1"
@@ "SequenceFlow_0rqes4b" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_19fg7gc" :> "Task_13r7bmt"
@@ "SequenceFlow_0upqxnz" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_0tbrrh9" :> "Task_10ik9d4"
@@ "SequenceFlow_0ye9pwd" :> "Task_06e9es5"
@@ "SequenceFlow_007i0gb" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_036yd4w" :> "Task_0zi619x"
@@ "SequenceFlow_1wxr7td" :> "Task_1ukgtgd"
@@ "SequenceFlow_1hrqezf" :> "Task_0k3desy"
@@ "SequenceFlow_12e7qby" :> "Task_0ieueaf"
@@ "SequenceFlow_09fa10u" :> "IntermediateCatchEvent_180guhd"
@@ "SequenceFlow_0cxrm8j" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_0lkr4ww" :> "IntermediateCatchEvent_0oxyhte"
@@ "SequenceFlow_1h50tfu" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_1nxvmw1" :> "ReceiveTask_146lfh4"
@@ "SequenceFlow_0f1t7q4" :> "EndEvent_0zeqiic"
@@ "SequenceFlow_1ssp09f" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_07c1y6g" :> "SendTask_1sfy3aq"
@@ "SequenceFlow_0woxsim" :> "ReceiveTask_1eiaojy"
@@ "SequenceFlow_1ifwhto" :> "SendTask_0bu2egl"
@@ "SequenceFlow_0ol0c8s" :> "EndEvent_0r34c4w"

CatN ==
   "Student_" :> Process
@@ "Company_" :> Process
@@ "InternshipOffice_" :> Process
@@ "InternshipDelegate_" :> Process
@@ "StartEvent_0efqept" :> NoneStartEvent
@@ "ExclusiveGateway_1pvytgl" :> ExclusiveOr
@@ "ExclusiveGateway_10r796g" :> ExclusiveOr
@@ "Task_05rcgao" :> AbstractTask
@@ "Task_12w7z0s" :> AbstractTask
@@ "Task_0kueqty" :> SendTask
@@ "Task_16mub7w" :> AbstractTask
@@ "Task_0y40xht" :> ReceiveTask
@@ "EndEvent_131pwct" :> NoneEndEvent
@@ "Task_1ukgtgd" :> SendTask
@@ "Task_0k3desy" :> SendTask
@@ "EndEvent_0g8hfyq" :> NoneEndEvent
@@ "Task_0z00tzq" :> SendTask
@@ "Task_1awa0vf" :> AbstractTask
@@ "Task_13r7bmt" :> SendTask
@@ "Task_10ik9d4" :> SendTask
@@ "Task_06e9es5" :> AbstractTask
@@ "Task_0zi619x" :> ReceiveTask
@@ "ExclusiveGateway_1ojvmkc" :> ExclusiveOr
@@ "Task_16a1dy1" :> AbstractTask
@@ "Task_0ieueaf" :> SendTask
@@ "StartEvent_1wgj96l" :> NoneStartEvent
@@ "ExclusiveGateway_1wor220" :> ExclusiveOr
@@ "IntermediateCatchEvent_180guhd" :> CatchMessageIntermediateEvent
@@ "IntermediateCatchEvent_0oxyhte" :> CatchMessageIntermediateEvent
@@ "ExclusiveGateway_025el3u" :> ExclusiveOr
@@ "ReceiveTask_146lfh4" :> ReceiveTask
@@ "EndEvent_0zeqiic" :> NoneEndEvent
@@ "StartEvent_0y07koo" :> MessageStartEvent
@@ "EventBasedGateway_1d92ix7" :> EventBased
@@ "StartEvent_0sg8ueb" :> MessageStartEvent
@@ "SendTask_0bu2egl" :> SendTask
@@ "ReceiveTask_1eiaojy" :> ReceiveTask
@@ "EndEvent_0r34c4w" :> NoneEndEvent
@@ "SendTask_1sfy3aq" :> AbstractTask

CatE ==
   "MessageFlow_1r2202w" :> MessageFlow
@@ "MessageFlow_0vajuh0" :> MessageFlow
@@ "MessageFlow_1exti3v" :> MessageFlow
@@ "MessageFlow_0whwr08" :> MessageFlow
@@ "MessageFlow_1uu4df2" :> MessageFlow
@@ "MessageFlow_0qzpag3" :> MessageFlow
@@ "MessageFlow_0n79ikw" :> MessageFlow
@@ "MessageFlow_0n7crx1" :> MessageFlow
@@ "SequenceFlow_19jde9o" :> NormalSeqFlow
@@ "SequenceFlow_07e105b" :> NormalSeqFlow
@@ "SequenceFlow_1nsmz5l" :> NormalSeqFlow
@@ "SequenceFlow_1a0w8i4" :> NormalSeqFlow
@@ "SequenceFlow_1hv2qod" :> NormalSeqFlow
@@ "SequenceFlow_04fa4c4" :> NormalSeqFlow
@@ "SequenceFlow_0epxxie" :> NormalSeqFlow
@@ "SequenceFlow_1716tm6" :> NormalSeqFlow
@@ "SequenceFlow_1e21rh4" :> NormalSeqFlow
@@ "SequenceFlow_0nlul5d" :> NormalSeqFlow
@@ "SequenceFlow_0oaajbr" :> NormalSeqFlow
@@ "SequenceFlow_1v26cki" :> NormalSeqFlow
@@ "SequenceFlow_0bferc8" :> NormalSeqFlow
@@ "SequenceFlow_0rqes4b" :> NormalSeqFlow
@@ "SequenceFlow_19fg7gc" :> NormalSeqFlow
@@ "SequenceFlow_0upqxnz" :> NormalSeqFlow
@@ "SequenceFlow_0tbrrh9" :> NormalSeqFlow
@@ "SequenceFlow_0ye9pwd" :> NormalSeqFlow
@@ "SequenceFlow_007i0gb" :> NormalSeqFlow
@@ "SequenceFlow_036yd4w" :> NormalSeqFlow
@@ "SequenceFlow_1wxr7td" :> NormalSeqFlow
@@ "SequenceFlow_1hrqezf" :> NormalSeqFlow
@@ "SequenceFlow_12e7qby" :> NormalSeqFlow
@@ "SequenceFlow_09fa10u" :> NormalSeqFlow
@@ "SequenceFlow_0cxrm8j" :> NormalSeqFlow
@@ "SequenceFlow_0lkr4ww" :> NormalSeqFlow
@@ "SequenceFlow_1h50tfu" :> NormalSeqFlow
@@ "SequenceFlow_1nxvmw1" :> NormalSeqFlow
@@ "SequenceFlow_0f1t7q4" :> NormalSeqFlow
@@ "SequenceFlow_1ssp09f" :> NormalSeqFlow
@@ "SequenceFlow_07c1y6g" :> NormalSeqFlow
@@ "SequenceFlow_0woxsim" :> NormalSeqFlow
@@ "SequenceFlow_1ifwhto" :> NormalSeqFlow
@@ "SequenceFlow_0ol0c8s" :> NormalSeqFlow

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

