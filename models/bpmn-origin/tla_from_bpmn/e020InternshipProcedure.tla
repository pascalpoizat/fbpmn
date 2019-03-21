---------------- MODULE e020InternshipProcedure ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

ContainRel ==
  "Process_0bvuk0f" :> { "IntermediateCatchEvent_180guhd", "IntermediateCatchEvent_0oxyhte", "ExclusiveGateway_025el3u", "ReceiveTask_146lfh4", "EndEvent_0zeqiic", "StartEvent_0y07koo", "EventBasedGateway_1d92ix7" }
  @@ "Process_0i8jx5m" :> { "StartEvent_0sg8ueb", "SendTask_0bu2egl", "ReceiveTask_1eiaojy", "EndEvent_0r34c4w", "SendTask_1sfy3aq" }
  @@ "Process_0xgexxt" :> { "StartEvent_0efqept", "ExclusiveGateway_1pvytgl", "ExclusiveGateway_10r796g", "Task_05rcgao", "Task_12w7z0s", "Task_0kueqty", "Task_16mub7w", "Task_0y40xht", "EndEvent_131pwct" }
  @@ "Process_158k3ep" :> { "Task_1ukgtgd", "Task_0k3desy", "EndEvent_0g8hfyq", "Task_0z00tzq", "Task_1awa0vf", "Task_13r7bmt", "Task_10ik9d4", "Task_06e9es5", "Task_0zi619x", "ExclusiveGateway_1ojvmkc", "Task_16a1dy1", "Task_0ieueaf", "StartEvent_1wgj96l", "ExclusiveGateway_1wor220" }

Node == {
  "Process_0xgexxt","Process_158k3ep","Process_0bvuk0f","Process_0i8jx5m","StartEvent_0efqept","ExclusiveGateway_1pvytgl","ExclusiveGateway_10r796g","Task_05rcgao","Task_12w7z0s","Task_0kueqty","Task_16mub7w","Task_0y40xht","EndEvent_131pwct","Task_1ukgtgd","Task_0k3desy","EndEvent_0g8hfyq","Task_0z00tzq","Task_1awa0vf","Task_13r7bmt","Task_10ik9d4","Task_06e9es5","Task_0zi619x","ExclusiveGateway_1ojvmkc","Task_16a1dy1","Task_0ieueaf","StartEvent_1wgj96l","ExclusiveGateway_1wor220","IntermediateCatchEvent_180guhd","IntermediateCatchEvent_0oxyhte","ExclusiveGateway_025el3u","ReceiveTask_146lfh4","EndEvent_0zeqiic","StartEvent_0y07koo","EventBasedGateway_1d92ix7","StartEvent_0sg8ueb","SendTask_0bu2egl","ReceiveTask_1eiaojy","EndEvent_0r34c4w","SendTask_1sfy3aq"
}

Edge == {
  "MessageFlow_1r2202w","MessageFlow_0vajuh0","MessageFlow_1exti3v","MessageFlow_0whwr08","MessageFlow_1uu4df2","MessageFlow_0qzpag3","MessageFlow_0n79ikw","MessageFlow_0n7crx1","SequenceFlow_1e21rh4","SequenceFlow_1716tm6","SequenceFlow_0epxxie","SequenceFlow_04fa4c4","SequenceFlow_1hv2qod","SequenceFlow_1a0w8i4","SequenceFlow_1nsmz5l","SequenceFlow_07e105b","SequenceFlow_19jde9o","SequenceFlow_12e7qby","SequenceFlow_1hrqezf","SequenceFlow_1wxr7td","SequenceFlow_036yd4w","SequenceFlow_007i0gb","SequenceFlow_0ye9pwd","SequenceFlow_0tbrrh9","SequenceFlow_0upqxnz","SequenceFlow_19fg7gc","SequenceFlow_0rqes4b","SequenceFlow_0bferc8","SequenceFlow_1v26cki","SequenceFlow_0oaajbr","SequenceFlow_0nlul5d","SequenceFlow_1ssp09f","SequenceFlow_0f1t7q4","SequenceFlow_1nxvmw1","SequenceFlow_1h50tfu","SequenceFlow_0lkr4ww","SequenceFlow_0cxrm8j","SequenceFlow_09fa10u","SequenceFlow_0ol0c8s","SequenceFlow_1ifwhto","SequenceFlow_0woxsim","SequenceFlow_07c1y6g"
}

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
@@ "SequenceFlow_1e21rh4" :> "Task_0kueqty"
@@ "SequenceFlow_1716tm6" :> "Task_16mub7w"
@@ "SequenceFlow_0epxxie" :> "StartEvent_0efqept"
@@ "SequenceFlow_04fa4c4" :> "Task_05rcgao"
@@ "SequenceFlow_1hv2qod" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_1a0w8i4" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_1nsmz5l" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_07e105b" :> "Task_12w7z0s"
@@ "SequenceFlow_19jde9o" :> "Task_0y40xht"
@@ "SequenceFlow_12e7qby" :> "StartEvent_1wgj96l"
@@ "SequenceFlow_1hrqezf" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_1wxr7td" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_036yd4w" :> "Task_13r7bmt"
@@ "SequenceFlow_007i0gb" :> "Task_0ieueaf"
@@ "SequenceFlow_0ye9pwd" :> "Task_0zi619x"
@@ "SequenceFlow_0tbrrh9" :> "Task_06e9es5"
@@ "SequenceFlow_0upqxnz" :> "Task_1ukgtgd"
@@ "SequenceFlow_19fg7gc" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_0rqes4b" :> "Task_0k3desy"
@@ "SequenceFlow_0bferc8" :> "Task_10ik9d4"
@@ "SequenceFlow_1v26cki" :> "Task_16a1dy1"
@@ "SequenceFlow_0oaajbr" :> "Task_1awa0vf"
@@ "SequenceFlow_0nlul5d" :> "Task_0z00tzq"
@@ "SequenceFlow_1ssp09f" :> "StartEvent_0y07koo"
@@ "SequenceFlow_0f1t7q4" :> "ReceiveTask_146lfh4"
@@ "SequenceFlow_1nxvmw1" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_1h50tfu" :> "IntermediateCatchEvent_0oxyhte"
@@ "SequenceFlow_0lkr4ww" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_0cxrm8j" :> "IntermediateCatchEvent_180guhd"
@@ "SequenceFlow_09fa10u" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_0ol0c8s" :> "SendTask_0bu2egl"
@@ "SequenceFlow_1ifwhto" :> "ReceiveTask_1eiaojy"
@@ "SequenceFlow_0woxsim" :> "SendTask_1sfy3aq"
@@ "SequenceFlow_07c1y6g" :> "StartEvent_0sg8ueb"

target ==
   "MessageFlow_1r2202w" :> "Task_0zi619x"
@@ "MessageFlow_0vajuh0" :> "ReceiveTask_1eiaojy"
@@ "MessageFlow_1exti3v" :> "Task_0y40xht"
@@ "MessageFlow_0whwr08" :> "StartEvent_0sg8ueb"
@@ "MessageFlow_1uu4df2" :> "IntermediateCatchEvent_180guhd"
@@ "MessageFlow_0qzpag3" :> "IntermediateCatchEvent_0oxyhte"
@@ "MessageFlow_0n79ikw" :> "ReceiveTask_146lfh4"
@@ "MessageFlow_0n7crx1" :> "StartEvent_0y07koo"
@@ "SequenceFlow_1e21rh4" :> "Task_12w7z0s"
@@ "SequenceFlow_1716tm6" :> "Task_0kueqty"
@@ "SequenceFlow_0epxxie" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_04fa4c4" :> "ExclusiveGateway_1pvytgl"
@@ "SequenceFlow_1hv2qod" :> "Task_05rcgao"
@@ "SequenceFlow_1a0w8i4" :> "ExclusiveGateway_10r796g"
@@ "SequenceFlow_1nsmz5l" :> "Task_16mub7w"
@@ "SequenceFlow_07e105b" :> "Task_0y40xht"
@@ "SequenceFlow_19jde9o" :> "EndEvent_131pwct"
@@ "SequenceFlow_12e7qby" :> "Task_0ieueaf"
@@ "SequenceFlow_1hrqezf" :> "Task_0k3desy"
@@ "SequenceFlow_1wxr7td" :> "Task_1ukgtgd"
@@ "SequenceFlow_036yd4w" :> "Task_0zi619x"
@@ "SequenceFlow_007i0gb" :> "ExclusiveGateway_1wor220"
@@ "SequenceFlow_0ye9pwd" :> "Task_06e9es5"
@@ "SequenceFlow_0tbrrh9" :> "Task_10ik9d4"
@@ "SequenceFlow_0upqxnz" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_19fg7gc" :> "Task_13r7bmt"
@@ "SequenceFlow_0rqes4b" :> "ExclusiveGateway_1ojvmkc"
@@ "SequenceFlow_0bferc8" :> "Task_16a1dy1"
@@ "SequenceFlow_1v26cki" :> "Task_1awa0vf"
@@ "SequenceFlow_0oaajbr" :> "Task_0z00tzq"
@@ "SequenceFlow_0nlul5d" :> "EndEvent_0g8hfyq"
@@ "SequenceFlow_1ssp09f" :> "EventBasedGateway_1d92ix7"
@@ "SequenceFlow_0f1t7q4" :> "EndEvent_0zeqiic"
@@ "SequenceFlow_1nxvmw1" :> "ReceiveTask_146lfh4"
@@ "SequenceFlow_1h50tfu" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_0lkr4ww" :> "IntermediateCatchEvent_0oxyhte"
@@ "SequenceFlow_0cxrm8j" :> "ExclusiveGateway_025el3u"
@@ "SequenceFlow_09fa10u" :> "IntermediateCatchEvent_180guhd"
@@ "SequenceFlow_0ol0c8s" :> "EndEvent_0r34c4w"
@@ "SequenceFlow_1ifwhto" :> "SendTask_0bu2egl"
@@ "SequenceFlow_0woxsim" :> "ReceiveTask_1eiaojy"
@@ "SequenceFlow_07c1y6g" :> "SendTask_1sfy3aq"

CatN ==
   "Process_0xgexxt" :> Process
@@ "Process_158k3ep" :> Process
@@ "Process_0bvuk0f" :> Process
@@ "Process_0i8jx5m" :> Process
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
@@ "EventBasedGateway_1d92ix7" :> EventBasedGateway
@@ "StartEvent_0sg8ueb" :> MessageStartEvent
@@ "SendTask_0bu2egl" :> SendTask
@@ "ReceiveTask_1eiaojy" :> ReceiveTask
@@ "EndEvent_0r34c4w" :> NoneEndEvent
@@ "SendTask_1sfy3aq" :> AbstractTask

CatE ==
   "MessageFlow_1r2202w" :> MsgFlow
@@ "MessageFlow_0vajuh0" :> MsgFlow
@@ "MessageFlow_1exti3v" :> MsgFlow
@@ "MessageFlow_0whwr08" :> MsgFlow
@@ "MessageFlow_1uu4df2" :> MsgFlow
@@ "MessageFlow_0qzpag3" :> MsgFlow
@@ "MessageFlow_0n79ikw" :> MsgFlow
@@ "MessageFlow_0n7crx1" :> MsgFlow
@@ "SequenceFlow_1e21rh4" :> NormalSeqFlow
@@ "SequenceFlow_1716tm6" :> NormalSeqFlow
@@ "SequenceFlow_0epxxie" :> NormalSeqFlow
@@ "SequenceFlow_04fa4c4" :> NormalSeqFlow
@@ "SequenceFlow_1hv2qod" :> NormalSeqFlow
@@ "SequenceFlow_1a0w8i4" :> NormalSeqFlow
@@ "SequenceFlow_1nsmz5l" :> NormalSeqFlow
@@ "SequenceFlow_07e105b" :> NormalSeqFlow
@@ "SequenceFlow_19jde9o" :> NormalSeqFlow
@@ "SequenceFlow_12e7qby" :> NormalSeqFlow
@@ "SequenceFlow_1hrqezf" :> NormalSeqFlow
@@ "SequenceFlow_1wxr7td" :> NormalSeqFlow
@@ "SequenceFlow_036yd4w" :> NormalSeqFlow
@@ "SequenceFlow_007i0gb" :> NormalSeqFlow
@@ "SequenceFlow_0ye9pwd" :> NormalSeqFlow
@@ "SequenceFlow_0tbrrh9" :> NormalSeqFlow
@@ "SequenceFlow_0upqxnz" :> NormalSeqFlow
@@ "SequenceFlow_19fg7gc" :> NormalSeqFlow
@@ "SequenceFlow_0rqes4b" :> NormalSeqFlow
@@ "SequenceFlow_0bferc8" :> NormalSeqFlow
@@ "SequenceFlow_1v26cki" :> NormalSeqFlow
@@ "SequenceFlow_0oaajbr" :> NormalSeqFlow
@@ "SequenceFlow_0nlul5d" :> NormalSeqFlow
@@ "SequenceFlow_1ssp09f" :> NormalSeqFlow
@@ "SequenceFlow_0f1t7q4" :> NormalSeqFlow
@@ "SequenceFlow_1nxvmw1" :> NormalSeqFlow
@@ "SequenceFlow_1h50tfu" :> NormalSeqFlow
@@ "SequenceFlow_0lkr4ww" :> NormalSeqFlow
@@ "SequenceFlow_0cxrm8j" :> NormalSeqFlow
@@ "SequenceFlow_09fa10u" :> NormalSeqFlow
@@ "SequenceFlow_0ol0c8s" :> NormalSeqFlow
@@ "SequenceFlow_1ifwhto" :> NormalSeqFlow
@@ "SequenceFlow_0woxsim" :> NormalSeqFlow
@@ "SequenceFlow_07c1y6g" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

CABoundaries ==
  [ i \in {} |-> {}]

WF == INSTANCE PWSWellFormed
ASSUME WF!WellFormedness

INSTANCE PWSSemantics

================================================================

