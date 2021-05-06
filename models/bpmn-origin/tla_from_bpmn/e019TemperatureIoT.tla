---------------- MODULE e019TemperatureIoT ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Boiller_" :> { "mf8", "mf7", "mf4" }
  @@ "Sensor_" :> { "mf6", "mf5" }
  @@ "Thermostat_" :> { "mf1", "mf2", "mf9" }
  @@ "User_" :> {  }
  @@ "WSNGateway_" :> { "mf3", "mf", "mf10" }

ContainRel ==
  "Boiller_" :> { "ExclusiveGateway_1feo3um", "ExclusiveGateway_0wtbkow", "ExclusiveGateway_0cpdpri", "IntermediateCatchEvent_1mqziug", "StartEvent_0tynlqh", "ExclusiveGateway_0sum07m", "Task_169t347", "ExclusiveGateway_19mjt5y", "EndEvent_0pa5oys", "Task_1e85hli", "Task_1spxdy2", "ExclusiveGateway_1izjr9z", "IntermediateThrowEvent_12cgsc9" }
  @@ "Sensor_" :> { "ExclusiveGateway_1alxwt7", "IntermediateThrowEvent_1ajpgtk", "EndEvent_0joc303", "ExclusiveGateway_0d9bxab", "StartEvent_12o3x3s", "Task_0aihuup", "Task_1p5k4vg" }
  @@ "Thermostat_" :> { "ExclusiveGateway_0uhrdet", "StartEvent_19zezl9", "ExclusiveGateway_0a5libn", "Task_01tkb3r", "IntermediateThrowEvent_0moj9p9", "ExclusiveGateway_1u3y4si", "EndEvent_14513uv", "IntermediateThrowEvent_1dkrxqj", "Task_0ca58zk" }
  @@ "User_" :> { "StartEvent_0mw9dyi", "Task_09igb82", "EndEvent_19aoxjz", "Task_1x71tep" }
  @@ "WSNGateway_" :> { "ReceiveTask_1cc6gb0", "ExclusiveGateway_186ksgk", "StartEvent_0tw9hoi", "Task_0amx3qc", "ExclusiveGateway_0h8c90b", "ExclusiveGateway_0qv0dm1", "IntermediateThrowEvent_1ab6lzx", "IntermediateThrowEvent_0zn5r2p", "ExclusiveGateway_04luead", "EndEvent_0wj7yv1", "Task_0yh5jmb", "ExclusiveGateway_1mr7igy", "Task_1pc6d9t", "ExclusiveGateway_0k9b245", "Task_18tknzx", "Task_1e6rsiy", "ExclusiveGateway_03bs3t5", "ExclusiveGateway_1t6g7zz", "ExclusiveGateway_0a8yao0", "ExclusiveGateway_095m84g", "Task_03ohewl", "IntermediateThrowEvent_1cd7dmz" }

Node == { "User_", "Thermostat_", "WSNGateway_", "Sensor_", "Boiller_", "StartEvent_0mw9dyi", "Task_09igb82", "EndEvent_19aoxjz", "Task_1x71tep", "ExclusiveGateway_0uhrdet", "StartEvent_19zezl9", "ExclusiveGateway_0a5libn", "Task_01tkb3r", "IntermediateThrowEvent_0moj9p9", "ExclusiveGateway_1u3y4si", "EndEvent_14513uv", "IntermediateThrowEvent_1dkrxqj", "Task_0ca58zk", "ReceiveTask_1cc6gb0", "ExclusiveGateway_186ksgk", "StartEvent_0tw9hoi", "Task_0amx3qc", "ExclusiveGateway_0h8c90b", "ExclusiveGateway_0qv0dm1", "IntermediateThrowEvent_1ab6lzx", "IntermediateThrowEvent_0zn5r2p", "ExclusiveGateway_04luead", "EndEvent_0wj7yv1", "Task_0yh5jmb", "ExclusiveGateway_1mr7igy", "Task_1pc6d9t", "ExclusiveGateway_0k9b245", "Task_18tknzx", "Task_1e6rsiy", "ExclusiveGateway_03bs3t5", "ExclusiveGateway_1t6g7zz", "ExclusiveGateway_0a8yao0", "ExclusiveGateway_095m84g", "Task_03ohewl", "IntermediateThrowEvent_1cd7dmz", "ExclusiveGateway_1alxwt7", "IntermediateThrowEvent_1ajpgtk", "EndEvent_0joc303", "ExclusiveGateway_0d9bxab", "StartEvent_12o3x3s", "Task_0aihuup", "Task_1p5k4vg", "ExclusiveGateway_1feo3um", "ExclusiveGateway_0wtbkow", "ExclusiveGateway_0cpdpri", "IntermediateCatchEvent_1mqziug", "StartEvent_0tynlqh", "ExclusiveGateway_0sum07m", "Task_169t347", "ExclusiveGateway_19mjt5y", "EndEvent_0pa5oys", "Task_1e85hli", "Task_1spxdy2", "ExclusiveGateway_1izjr9z", "IntermediateThrowEvent_12cgsc9" }

Edge == { "MessageFlow_18pje80", "MessageFlow_1jgvn81", "MessageFlow_0vinqwi", "MessageFlow_0vwhu1f", "MessageFlow_1bpo13k", "MessageFlow_1hyly74", "MessageFlow_0aje9sn", "MessageFlow_1o3tyk4", "MessageFlow_0nqzifu", "MessageFlow_0dguqk7", "MessageFlow_00ca6vp", "SequenceFlow_1ngsqgy", "SequenceFlow_02i1zog", "SequenceFlow_1uup9ft", "SequenceFlow_0mr13bl", "SequenceFlow_0ilol45", "SequenceFlow_1fvktk8", "SequenceFlow_07vsnao", "SequenceFlow_1kk1jne", "SequenceFlow_0vwirsp", "SequenceFlow_0wqy81u", "SequenceFlow_1rpwomj", "SequenceFlow_0j7d6k8", "SequenceFlow_1quu0wg", "SequenceFlow_14zismf", "SequenceFlow_0tbx7nt", "SequenceFlow_1n4vv49", "SequenceFlow_1lr4cps", "SequenceFlow_1017nuh", "SequenceFlow_15ortkr", "SequenceFlow_1pvrfjg", "SequenceFlow_0yclgws", "SequenceFlow_0ipzp9y", "SequenceFlow_1nacukm", "SequenceFlow_1w9mr57", "SequenceFlow_1o0bwvr", "SequenceFlow_17faiz5", "SequenceFlow_07ahv22", "SequenceFlow_1nnne6n", "SequenceFlow_0n8zfgy", "SequenceFlow_0ha4jhs", "SequenceFlow_04p0en0", "SequenceFlow_17eb2ri", "SequenceFlow_0vmtagi", "SequenceFlow_1t7zsjn", "SequenceFlow_1715hka", "SequenceFlow_1pvcw5e", "SequenceFlow_1vmz2u9", "SequenceFlow_112gnsc", "SequenceFlow_0477vxz", "SequenceFlow_0rdqb09", "SequenceFlow_07gw8yk", "SequenceFlow_0jioz8d", "SequenceFlow_127z28e", "SequenceFlow_1dhqk99", "SequenceFlow_0v1itpk", "SequenceFlow_0j98n24", "SequenceFlow_15jyzqg", "SequenceFlow_05ihnu4", "SequenceFlow_1dtybq7", "SequenceFlow_0eoboyu", "SequenceFlow_0jy3w8q", "SequenceFlow_0u67u7k", "SequenceFlow_1plf2me", "SequenceFlow_0ik719b", "SequenceFlow_18i2li3", "SequenceFlow_1j073vl", "SequenceFlow_04ctmhl", "SequenceFlow_00sw0ns", "SequenceFlow_151xud0", "SequenceFlow_0yf7004", "SequenceFlow_1tu3a1o", "SequenceFlow_0so9y7c" }

Message == { "mf1", "mf2", "mf", "mf5", "mf4", "mf10", "mf8", "mf9", "mf3", "mf7", "mf6" }

msgtype ==
   "MessageFlow_18pje80" :> "mf1"
@@ "MessageFlow_1jgvn81" :> "mf2"
@@ "MessageFlow_0vinqwi" :> "mf"
@@ "MessageFlow_0vwhu1f" :> "mf5"
@@ "MessageFlow_1bpo13k" :> "mf4"
@@ "MessageFlow_1hyly74" :> "mf10"
@@ "MessageFlow_0aje9sn" :> "mf8"
@@ "MessageFlow_1o3tyk4" :> "mf9"
@@ "MessageFlow_0nqzifu" :> "mf3"
@@ "MessageFlow_0dguqk7" :> "mf7"
@@ "MessageFlow_00ca6vp" :> "mf6"


source ==
   "MessageFlow_18pje80" :> "Task_09igb82"
@@ "MessageFlow_1jgvn81" :> "Task_1x71tep"
@@ "MessageFlow_0vinqwi" :> "Task_01tkb3r"
@@ "MessageFlow_0vwhu1f" :> "ReceiveTask_1cc6gb0"
@@ "MessageFlow_1bpo13k" :> "Task_0amx3qc"
@@ "MessageFlow_1hyly74" :> "Task_1p5k4vg"
@@ "MessageFlow_0aje9sn" :> "Task_0yh5jmb"
@@ "MessageFlow_1o3tyk4" :> "Task_18tknzx"
@@ "MessageFlow_0nqzifu" :> "IntermediateThrowEvent_0moj9p9"
@@ "MessageFlow_0dguqk7" :> "IntermediateThrowEvent_1ab6lzx"
@@ "MessageFlow_00ca6vp" :> "IntermediateThrowEvent_0zn5r2p"
@@ "SequenceFlow_1ngsqgy" :> "Task_1x71tep"
@@ "SequenceFlow_02i1zog" :> "Task_09igb82"
@@ "SequenceFlow_1uup9ft" :> "StartEvent_0mw9dyi"
@@ "SequenceFlow_0mr13bl" :> "ExclusiveGateway_0uhrdet"
@@ "SequenceFlow_0ilol45" :> "Task_0ca58zk"
@@ "SequenceFlow_1fvktk8" :> "ExclusiveGateway_1u3y4si"
@@ "SequenceFlow_07vsnao" :> "Task_01tkb3r"
@@ "SequenceFlow_1kk1jne" :> "IntermediateThrowEvent_0moj9p9"
@@ "SequenceFlow_0vwirsp" :> "IntermediateThrowEvent_1dkrxqj"
@@ "SequenceFlow_0wqy81u" :> "ExclusiveGateway_0a5libn"
@@ "SequenceFlow_1rpwomj" :> "ExclusiveGateway_0a5libn"
@@ "SequenceFlow_0j7d6k8" :> "StartEvent_19zezl9"
@@ "SequenceFlow_1quu0wg" :> "ExclusiveGateway_04luead"
@@ "SequenceFlow_14zismf" :> "IntermediateThrowEvent_0zn5r2p"
@@ "SequenceFlow_0tbx7nt" :> "IntermediateThrowEvent_1ab6lzx"
@@ "SequenceFlow_1n4vv49" :> "ExclusiveGateway_0qv0dm1"
@@ "SequenceFlow_1lr4cps" :> "ExclusiveGateway_0qv0dm1"
@@ "SequenceFlow_1017nuh" :> "IntermediateThrowEvent_1cd7dmz"
@@ "SequenceFlow_15ortkr" :> "Task_0yh5jmb"
@@ "SequenceFlow_1pvrfjg" :> "ExclusiveGateway_1t6g7zz"
@@ "SequenceFlow_0yclgws" :> "ExclusiveGateway_03bs3t5"
@@ "SequenceFlow_0ipzp9y" :> "Task_1e6rsiy"
@@ "SequenceFlow_1nacukm" :> "Task_18tknzx"
@@ "SequenceFlow_1w9mr57" :> "ExclusiveGateway_0a8yao0"
@@ "SequenceFlow_1o0bwvr" :> "ExclusiveGateway_0k9b245"
@@ "SequenceFlow_17faiz5" :> "ExclusiveGateway_0k9b245"
@@ "SequenceFlow_07ahv22" :> "Task_1pc6d9t"
@@ "SequenceFlow_1nnne6n" :> "ExclusiveGateway_1mr7igy"
@@ "SequenceFlow_0n8zfgy" :> "ExclusiveGateway_03bs3t5"
@@ "SequenceFlow_0ha4jhs" :> "ExclusiveGateway_0h8c90b"
@@ "SequenceFlow_04p0en0" :> "ExclusiveGateway_095m84g"
@@ "SequenceFlow_17eb2ri" :> "ExclusiveGateway_0h8c90b"
@@ "SequenceFlow_0vmtagi" :> "Task_03ohewl"
@@ "SequenceFlow_1t7zsjn" :> "ReceiveTask_1cc6gb0"
@@ "SequenceFlow_1715hka" :> "Task_0amx3qc"
@@ "SequenceFlow_1pvcw5e" :> "ExclusiveGateway_186ksgk"
@@ "SequenceFlow_1vmz2u9" :> "ExclusiveGateway_186ksgk"
@@ "SequenceFlow_112gnsc" :> "ExclusiveGateway_186ksgk"
@@ "SequenceFlow_0477vxz" :> "StartEvent_0tw9hoi"
@@ "SequenceFlow_0rdqb09" :> "Task_1p5k4vg"
@@ "SequenceFlow_07gw8yk" :> "Task_0aihuup"
@@ "SequenceFlow_0jioz8d" :> "ExclusiveGateway_0d9bxab"
@@ "SequenceFlow_127z28e" :> "ExclusiveGateway_1alxwt7"
@@ "SequenceFlow_1dhqk99" :> "IntermediateThrowEvent_1ajpgtk"
@@ "SequenceFlow_0v1itpk" :> "ExclusiveGateway_1alxwt7"
@@ "SequenceFlow_0j98n24" :> "StartEvent_12o3x3s"
@@ "SequenceFlow_15jyzqg" :> "ExclusiveGateway_19mjt5y"
@@ "SequenceFlow_05ihnu4" :> "ExclusiveGateway_1izjr9z"
@@ "SequenceFlow_1dtybq7" :> "Task_1e85hli"
@@ "SequenceFlow_0eoboyu" :> "Task_1spxdy2"
@@ "SequenceFlow_0jy3w8q" :> "IntermediateCatchEvent_1mqziug"
@@ "SequenceFlow_0u67u7k" :> "ExclusiveGateway_19mjt5y"
@@ "SequenceFlow_1plf2me" :> "ExclusiveGateway_19mjt5y"
@@ "SequenceFlow_0ik719b" :> "Task_169t347"
@@ "SequenceFlow_18i2li3" :> "ExclusiveGateway_0sum07m"
@@ "SequenceFlow_1j073vl" :> "ExclusiveGateway_0cpdpri"
@@ "SequenceFlow_04ctmhl" :> "ExclusiveGateway_0cpdpri"
@@ "SequenceFlow_00sw0ns" :> "IntermediateThrowEvent_12cgsc9"
@@ "SequenceFlow_151xud0" :> "ExclusiveGateway_0wtbkow"
@@ "SequenceFlow_0yf7004" :> "ExclusiveGateway_0wtbkow"
@@ "SequenceFlow_1tu3a1o" :> "ExclusiveGateway_1feo3um"
@@ "SequenceFlow_0so9y7c" :> "StartEvent_0tynlqh"

target ==
   "MessageFlow_18pje80" :> "StartEvent_19zezl9"
@@ "MessageFlow_1jgvn81" :> "IntermediateThrowEvent_1dkrxqj"
@@ "MessageFlow_0vinqwi" :> "StartEvent_0tw9hoi"
@@ "MessageFlow_0vwhu1f" :> "StartEvent_12o3x3s"
@@ "MessageFlow_1bpo13k" :> "StartEvent_0tynlqh"
@@ "MessageFlow_1hyly74" :> "Task_1pc6d9t"
@@ "MessageFlow_0aje9sn" :> "IntermediateThrowEvent_12cgsc9"
@@ "MessageFlow_1o3tyk4" :> "Task_0ca58zk"
@@ "MessageFlow_0nqzifu" :> "IntermediateThrowEvent_1cd7dmz"
@@ "MessageFlow_0dguqk7" :> "IntermediateCatchEvent_1mqziug"
@@ "MessageFlow_00ca6vp" :> "IntermediateThrowEvent_1ajpgtk"
@@ "SequenceFlow_1ngsqgy" :> "EndEvent_19aoxjz"
@@ "SequenceFlow_02i1zog" :> "Task_1x71tep"
@@ "SequenceFlow_1uup9ft" :> "Task_09igb82"
@@ "SequenceFlow_0mr13bl" :> "ExclusiveGateway_1u3y4si"
@@ "SequenceFlow_0ilol45" :> "ExclusiveGateway_0uhrdet"
@@ "SequenceFlow_1fvktk8" :> "Task_0ca58zk"
@@ "SequenceFlow_07vsnao" :> "ExclusiveGateway_1u3y4si"
@@ "SequenceFlow_1kk1jne" :> "EndEvent_14513uv"
@@ "SequenceFlow_0vwirsp" :> "IntermediateThrowEvent_0moj9p9"
@@ "SequenceFlow_0wqy81u" :> "Task_01tkb3r"
@@ "SequenceFlow_1rpwomj" :> "IntermediateThrowEvent_1dkrxqj"
@@ "SequenceFlow_0j7d6k8" :> "ExclusiveGateway_0a5libn"
@@ "SequenceFlow_1quu0wg" :> "EndEvent_0wj7yv1"
@@ "SequenceFlow_14zismf" :> "ExclusiveGateway_04luead"
@@ "SequenceFlow_0tbx7nt" :> "ExclusiveGateway_04luead"
@@ "SequenceFlow_1n4vv49" :> "IntermediateThrowEvent_0zn5r2p"
@@ "SequenceFlow_1lr4cps" :> "IntermediateThrowEvent_1ab6lzx"
@@ "SequenceFlow_1017nuh" :> "ExclusiveGateway_0qv0dm1"
@@ "SequenceFlow_15ortkr" :> "ExclusiveGateway_095m84g"
@@ "SequenceFlow_1pvrfjg" :> "ExclusiveGateway_0a8yao0"
@@ "SequenceFlow_0yclgws" :> "ExclusiveGateway_1t6g7zz"
@@ "SequenceFlow_0ipzp9y" :> "ExclusiveGateway_1t6g7zz"
@@ "SequenceFlow_1nacukm" :> "ExclusiveGateway_0a8yao0"
@@ "SequenceFlow_1w9mr57" :> "ExclusiveGateway_1mr7igy"
@@ "SequenceFlow_1o0bwvr" :> "Task_03ohewl"
@@ "SequenceFlow_17faiz5" :> "Task_18tknzx"
@@ "SequenceFlow_07ahv22" :> "ExclusiveGateway_0k9b245"
@@ "SequenceFlow_1nnne6n" :> "Task_0yh5jmb"
@@ "SequenceFlow_0n8zfgy" :> "Task_1e6rsiy"
@@ "SequenceFlow_0ha4jhs" :> "ExclusiveGateway_1mr7igy"
@@ "SequenceFlow_04p0en0" :> "Task_1pc6d9t"
@@ "SequenceFlow_17eb2ri" :> "ExclusiveGateway_095m84g"
@@ "SequenceFlow_0vmtagi" :> "ExclusiveGateway_03bs3t5"
@@ "SequenceFlow_1t7zsjn" :> "ExclusiveGateway_0h8c90b"
@@ "SequenceFlow_1715hka" :> "ExclusiveGateway_0h8c90b"
@@ "SequenceFlow_1pvcw5e" :> "Task_0amx3qc"
@@ "SequenceFlow_1vmz2u9" :> "IntermediateThrowEvent_1cd7dmz"
@@ "SequenceFlow_112gnsc" :> "ReceiveTask_1cc6gb0"
@@ "SequenceFlow_0477vxz" :> "ExclusiveGateway_186ksgk"
@@ "SequenceFlow_0rdqb09" :> "ExclusiveGateway_0d9bxab"
@@ "SequenceFlow_07gw8yk" :> "Task_1p5k4vg"
@@ "SequenceFlow_0jioz8d" :> "Task_0aihuup"
@@ "SequenceFlow_127z28e" :> "ExclusiveGateway_0d9bxab"
@@ "SequenceFlow_1dhqk99" :> "EndEvent_0joc303"
@@ "SequenceFlow_0v1itpk" :> "IntermediateThrowEvent_1ajpgtk"
@@ "SequenceFlow_0j98n24" :> "ExclusiveGateway_1alxwt7"
@@ "SequenceFlow_15jyzqg" :> "ExclusiveGateway_1izjr9z"
@@ "SequenceFlow_05ihnu4" :> "ExclusiveGateway_0sum07m"
@@ "SequenceFlow_1dtybq7" :> "ExclusiveGateway_1izjr9z"
@@ "SequenceFlow_0eoboyu" :> "ExclusiveGateway_1izjr9z"
@@ "SequenceFlow_0jy3w8q" :> "EndEvent_0pa5oys"
@@ "SequenceFlow_0u67u7k" :> "Task_1e85hli"
@@ "SequenceFlow_1plf2me" :> "Task_1spxdy2"
@@ "SequenceFlow_0ik719b" :> "ExclusiveGateway_19mjt5y"
@@ "SequenceFlow_18i2li3" :> "Task_169t347"
@@ "SequenceFlow_1j073vl" :> "ExclusiveGateway_0sum07m"
@@ "SequenceFlow_04ctmhl" :> "ExclusiveGateway_1feo3um"
@@ "SequenceFlow_00sw0ns" :> "ExclusiveGateway_0cpdpri"
@@ "SequenceFlow_151xud0" :> "IntermediateCatchEvent_1mqziug"
@@ "SequenceFlow_0yf7004" :> "IntermediateThrowEvent_12cgsc9"
@@ "SequenceFlow_1tu3a1o" :> "ExclusiveGateway_0wtbkow"
@@ "SequenceFlow_0so9y7c" :> "ExclusiveGateway_1feo3um"

CatN ==
   "User_" :> Process
@@ "Thermostat_" :> Process
@@ "WSNGateway_" :> Process
@@ "Sensor_" :> Process
@@ "Boiller_" :> Process
@@ "StartEvent_0mw9dyi" :> NoneStartEvent
@@ "Task_09igb82" :> SendTask
@@ "EndEvent_19aoxjz" :> NoneEndEvent
@@ "Task_1x71tep" :> SendTask
@@ "ExclusiveGateway_0uhrdet" :> ExclusiveOr
@@ "StartEvent_19zezl9" :> MessageStartEvent
@@ "ExclusiveGateway_0a5libn" :> Parallel
@@ "Task_01tkb3r" :> SendTask
@@ "IntermediateThrowEvent_0moj9p9" :> ThrowMessageIntermediateEvent
@@ "ExclusiveGateway_1u3y4si" :> ExclusiveOr
@@ "EndEvent_14513uv" :> TerminateEndEvent
@@ "IntermediateThrowEvent_1dkrxqj" :> CatchMessageIntermediateEvent
@@ "Task_0ca58zk" :> ReceiveTask
@@ "ReceiveTask_1cc6gb0" :> SendTask
@@ "ExclusiveGateway_186ksgk" :> Parallel
@@ "StartEvent_0tw9hoi" :> MessageStartEvent
@@ "Task_0amx3qc" :> SendTask
@@ "ExclusiveGateway_0h8c90b" :> Parallel
@@ "ExclusiveGateway_0qv0dm1" :> Parallel
@@ "IntermediateThrowEvent_1ab6lzx" :> ThrowMessageIntermediateEvent
@@ "IntermediateThrowEvent_0zn5r2p" :> ThrowMessageIntermediateEvent
@@ "ExclusiveGateway_04luead" :> Parallel
@@ "EndEvent_0wj7yv1" :> TerminateEndEvent
@@ "Task_0yh5jmb" :> SendTask
@@ "ExclusiveGateway_1mr7igy" :> ExclusiveOr
@@ "Task_1pc6d9t" :> ReceiveTask
@@ "ExclusiveGateway_0k9b245" :> Parallel
@@ "Task_18tknzx" :> SendTask
@@ "Task_1e6rsiy" :> AbstractTask
@@ "ExclusiveGateway_03bs3t5" :> ExclusiveOr
@@ "ExclusiveGateway_1t6g7zz" :> ExclusiveOr
@@ "ExclusiveGateway_0a8yao0" :> Parallel
@@ "ExclusiveGateway_095m84g" :> ExclusiveOr
@@ "Task_03ohewl" :> AbstractTask
@@ "IntermediateThrowEvent_1cd7dmz" :> CatchMessageIntermediateEvent
@@ "ExclusiveGateway_1alxwt7" :> Parallel
@@ "IntermediateThrowEvent_1ajpgtk" :> CatchMessageIntermediateEvent
@@ "EndEvent_0joc303" :> TerminateEndEvent
@@ "ExclusiveGateway_0d9bxab" :> ExclusiveOr
@@ "StartEvent_12o3x3s" :> MessageStartEvent
@@ "Task_0aihuup" :> AbstractTask
@@ "Task_1p5k4vg" :> SendTask
@@ "ExclusiveGateway_1feo3um" :> ExclusiveOr
@@ "ExclusiveGateway_0wtbkow" :> EventBased
@@ "ExclusiveGateway_0cpdpri" :> Parallel
@@ "IntermediateCatchEvent_1mqziug" :> CatchMessageIntermediateEvent
@@ "StartEvent_0tynlqh" :> MessageStartEvent
@@ "ExclusiveGateway_0sum07m" :> ExclusiveOr
@@ "Task_169t347" :> AbstractTask
@@ "ExclusiveGateway_19mjt5y" :> ExclusiveOr
@@ "EndEvent_0pa5oys" :> TerminateEndEvent
@@ "Task_1e85hli" :> AbstractTask
@@ "Task_1spxdy2" :> AbstractTask
@@ "ExclusiveGateway_1izjr9z" :> ExclusiveOr
@@ "IntermediateThrowEvent_12cgsc9" :> CatchMessageIntermediateEvent

CatE ==
   "MessageFlow_18pje80" :> MessageFlow
@@ "MessageFlow_1jgvn81" :> MessageFlow
@@ "MessageFlow_0vinqwi" :> MessageFlow
@@ "MessageFlow_0vwhu1f" :> MessageFlow
@@ "MessageFlow_1bpo13k" :> MessageFlow
@@ "MessageFlow_1hyly74" :> MessageFlow
@@ "MessageFlow_0aje9sn" :> MessageFlow
@@ "MessageFlow_1o3tyk4" :> MessageFlow
@@ "MessageFlow_0nqzifu" :> MessageFlow
@@ "MessageFlow_0dguqk7" :> MessageFlow
@@ "MessageFlow_00ca6vp" :> MessageFlow
@@ "SequenceFlow_1ngsqgy" :> NormalSeqFlow
@@ "SequenceFlow_02i1zog" :> NormalSeqFlow
@@ "SequenceFlow_1uup9ft" :> NormalSeqFlow
@@ "SequenceFlow_0mr13bl" :> NormalSeqFlow
@@ "SequenceFlow_0ilol45" :> NormalSeqFlow
@@ "SequenceFlow_1fvktk8" :> NormalSeqFlow
@@ "SequenceFlow_07vsnao" :> NormalSeqFlow
@@ "SequenceFlow_1kk1jne" :> NormalSeqFlow
@@ "SequenceFlow_0vwirsp" :> NormalSeqFlow
@@ "SequenceFlow_0wqy81u" :> NormalSeqFlow
@@ "SequenceFlow_1rpwomj" :> NormalSeqFlow
@@ "SequenceFlow_0j7d6k8" :> NormalSeqFlow
@@ "SequenceFlow_1quu0wg" :> NormalSeqFlow
@@ "SequenceFlow_14zismf" :> NormalSeqFlow
@@ "SequenceFlow_0tbx7nt" :> NormalSeqFlow
@@ "SequenceFlow_1n4vv49" :> NormalSeqFlow
@@ "SequenceFlow_1lr4cps" :> NormalSeqFlow
@@ "SequenceFlow_1017nuh" :> NormalSeqFlow
@@ "SequenceFlow_15ortkr" :> NormalSeqFlow
@@ "SequenceFlow_1pvrfjg" :> NormalSeqFlow
@@ "SequenceFlow_0yclgws" :> DefaultSeqFlow
@@ "SequenceFlow_0ipzp9y" :> NormalSeqFlow
@@ "SequenceFlow_1nacukm" :> NormalSeqFlow
@@ "SequenceFlow_1w9mr57" :> NormalSeqFlow
@@ "SequenceFlow_1o0bwvr" :> NormalSeqFlow
@@ "SequenceFlow_17faiz5" :> NormalSeqFlow
@@ "SequenceFlow_07ahv22" :> NormalSeqFlow
@@ "SequenceFlow_1nnne6n" :> NormalSeqFlow
@@ "SequenceFlow_0n8zfgy" :> ConditionalSeqFlow
@@ "SequenceFlow_0ha4jhs" :> NormalSeqFlow
@@ "SequenceFlow_04p0en0" :> NormalSeqFlow
@@ "SequenceFlow_17eb2ri" :> NormalSeqFlow
@@ "SequenceFlow_0vmtagi" :> NormalSeqFlow
@@ "SequenceFlow_1t7zsjn" :> NormalSeqFlow
@@ "SequenceFlow_1715hka" :> NormalSeqFlow
@@ "SequenceFlow_1pvcw5e" :> NormalSeqFlow
@@ "SequenceFlow_1vmz2u9" :> NormalSeqFlow
@@ "SequenceFlow_112gnsc" :> NormalSeqFlow
@@ "SequenceFlow_0477vxz" :> NormalSeqFlow
@@ "SequenceFlow_0rdqb09" :> NormalSeqFlow
@@ "SequenceFlow_07gw8yk" :> NormalSeqFlow
@@ "SequenceFlow_0jioz8d" :> NormalSeqFlow
@@ "SequenceFlow_127z28e" :> NormalSeqFlow
@@ "SequenceFlow_1dhqk99" :> NormalSeqFlow
@@ "SequenceFlow_0v1itpk" :> NormalSeqFlow
@@ "SequenceFlow_0j98n24" :> NormalSeqFlow
@@ "SequenceFlow_15jyzqg" :> DefaultSeqFlow
@@ "SequenceFlow_05ihnu4" :> NormalSeqFlow
@@ "SequenceFlow_1dtybq7" :> NormalSeqFlow
@@ "SequenceFlow_0eoboyu" :> NormalSeqFlow
@@ "SequenceFlow_0jy3w8q" :> NormalSeqFlow
@@ "SequenceFlow_0u67u7k" :> ConditionalSeqFlow
@@ "SequenceFlow_1plf2me" :> ConditionalSeqFlow
@@ "SequenceFlow_0ik719b" :> NormalSeqFlow
@@ "SequenceFlow_18i2li3" :> NormalSeqFlow
@@ "SequenceFlow_1j073vl" :> NormalSeqFlow
@@ "SequenceFlow_04ctmhl" :> NormalSeqFlow
@@ "SequenceFlow_00sw0ns" :> NormalSeqFlow
@@ "SequenceFlow_151xud0" :> NormalSeqFlow
@@ "SequenceFlow_0yf7004" :> NormalSeqFlow
@@ "SequenceFlow_1tu3a1o" :> NormalSeqFlow
@@ "SequenceFlow_0so9y7c" :> NormalSeqFlow

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

