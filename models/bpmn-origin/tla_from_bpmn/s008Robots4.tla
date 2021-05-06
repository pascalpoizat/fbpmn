---------------- MODULE s008Robots4 ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "ControllerId" :> { "ACKP", "ACKS", "ERRP", "ERRS" }
  @@ "PlanterId" :> { "DIRECTP", "ACTIVATEP", "DEACTIVATEP" }
  @@ "SprayerId" :> { "ACTIVATES", "DEACTIVATES", "DIRECTS" }

ContainRel ==
  "Activity_0m6r7aa" :> { "Event_1agw4ay", "Event_14i96pr", "Gateway_1m7b2rp", "Activity_0byesng", "Gateway_1isams0", "Event_1os5ssu", "Event_164f6ag", "Gateway_0ehzoat", "Event_0vgg0ba", "Event_0ze20ps" }
  @@ "Activity_0xuomcr" :> { "StartEvent_1", "Event_0bxauwm", "Gateway_0qgs992", "Activity_0id691h", "Gateway_0wl6a1o", "Event_1et46oa", "Event_1pwlc9i", "Gateway_0ok6126", "Event_0gwjxex", "Event_1i5je9n" }
  @@ "Activity_1bln3fh" :> { "Event_0kujun6", "Activity_1qnb9i2", "Gateway_11qodf7", "Event_0r02vo3", "Event_0oj4f06", "Gateway_0q68aki", "Gateway_08a4yuy", "Activity_03ue3iv", "Activity_196ygfc" }
  @@ "Activity_1jcadcm" :> { "Event_0syt2y2", "Activity_0jootbn", "Gateway_0nml6ij", "Event_03je60h", "Event_0kegwa2", "Gateway_0hg0uq5", "Gateway_1xyjdit", "Activity_1xs44yy", "Activity_01kew4w" }
  @@ "ControllerId" :> { "Event_1ac2z2i", "Gateway_1ub2ltv", "Activity_0xuomcr", "Activity_0m6r7aa", "Event_1bkshv0", "Gateway_0ki8tki" }
  @@ "PlanterId" :> { "Event_1matb53", "Activity_0c5l85e", "Activity_1jcadcm", "Event_1k7stxl", "Gateway_0nq1hkt", "Activity_04y084u", "Event_0ci0tt9", "Activity_00galsb", "Activity_0c215j4", "Event_13r5sdw" }
  @@ "SprayerId" :> { "Event_1900qpj", "Activity_08iyx19", "Event_04no4fg", "Gateway_0y1d8f6", "Activity_0ioiiue", "Event_03mrlm4", "Activity_0plaha5", "Activity_0x9tdqh", "Activity_1bln3fh", "Event_10886de" }

Node == { "ControllerId", "PlanterId", "SprayerId", "Event_1ac2z2i", "Gateway_1ub2ltv", "Activity_0xuomcr", "Activity_0m6r7aa", "Event_1bkshv0", "Gateway_0ki8tki", "StartEvent_1", "Event_0bxauwm", "Gateway_0qgs992", "Activity_0id691h", "Gateway_0wl6a1o", "Event_1et46oa", "Event_1pwlc9i", "Gateway_0ok6126", "Event_0gwjxex", "Event_1i5je9n", "Event_1agw4ay", "Event_14i96pr", "Gateway_1m7b2rp", "Activity_0byesng", "Gateway_1isams0", "Event_1os5ssu", "Event_164f6ag", "Gateway_0ehzoat", "Event_0vgg0ba", "Event_0ze20ps", "Event_1matb53", "Activity_0c5l85e", "Activity_1jcadcm", "Event_1k7stxl", "Gateway_0nq1hkt", "Activity_04y084u", "Event_0ci0tt9", "Activity_00galsb", "Activity_0c215j4", "Event_13r5sdw", "Event_0syt2y2", "Activity_0jootbn", "Gateway_0nml6ij", "Event_03je60h", "Event_0kegwa2", "Gateway_0hg0uq5", "Gateway_1xyjdit", "Activity_1xs44yy", "Activity_01kew4w", "Event_1900qpj", "Activity_08iyx19", "Event_04no4fg", "Gateway_0y1d8f6", "Activity_0ioiiue", "Event_03mrlm4", "Activity_0plaha5", "Activity_0x9tdqh", "Activity_1bln3fh", "Event_10886de", "Event_0kujun6", "Activity_1qnb9i2", "Gateway_11qodf7", "Event_0r02vo3", "Event_0oj4f06", "Gateway_0q68aki", "Gateway_08a4yuy", "Activity_03ue3iv", "Activity_196ygfc" }

Edge == { "Flow_1c80fvc", "Flow_1q3i58t", "Flow_05gqmpv", "Flow_0ehcsg3", "Flow_03khyvp", "Flow_0guolab", "Flow_1g4l0c0", "Flow_0m56orh", "Flow_15a2gh1", "Flow_08aidsp", "Flow_01xnorx", "Flow_12fakd2", "Flow_1rbt7hr", "Flow_10ytow4", "Flow_0p2qd4k", "Flow_0q0qopg", "Flow_1maux1g", "Flow_0ep8hv4", "Flow_1wf4er6", "Flow_10neqt1", "Flow_04ffiyw", "Flow_0qdi3sr", "Flow_1mj2hsk", "Flow_07deyd6", "Flow_0gh7btl", "Flow_00b7crz", "Flow_0lbxlpn", "Flow_0g038fl", "Flow_0p1txzr", "Flow_1pb2ee9", "Flow_143f8dn", "Flow_104cjar", "Flow_1sf54qd", "Flow_1qn4k7o", "Flow_0mxan7e", "Flow_0d4ra5x", "Flow_14e42wb", "Flow_1p21xfx", "Flow_0i8hiam", "Flow_14hbae4", "Flow_1n1ra56", "Flow_0qbvxf7", "Flow_1skh2ra", "Flow_1wczndj", "Flow_0drx7uh", "Flow_0ik7oa8", "Flow_1alj9in", "Flow_0q7wp3m", "Flow_0l3fimu", "Flow_1rsrumf", "Flow_0owe6ra", "Flow_1p7v2y8", "Flow_12jkr8q", "Flow_17fyu56", "Flow_1alyuap", "Flow_0099ioz", "Flow_0wycw1f", "Flow_1fb9j2l", "Flow_002vf6t", "Flow_1io6s2v", "Flow_0jot9v9", "Flow_11tz16c", "Flow_1nsyl9j", "Flow_0x8186j", "Flow_0a37bd8", "Flow_1rxk6wy", "Flow_0gir2eb", "Flow_14t1xp3", "Flow_0oeg7jv", "Flow_11u1vn6", "Flow_0jh8c89", "Flow_0y7com1", "Flow_15sulbd", "Flow_0qhwa2b" }

Message == { "ACTIVATEP", "DEACTIVATEP", "DIRECTP", "ERRP", "ACKP", "ACTIVATES", "DIRECTS", "DEACTIVATES", "ERRS", "ACKS" }

msgtype ==
   "Flow_1c80fvc" :> "ACTIVATEP"
@@ "Flow_1q3i58t" :> "DEACTIVATEP"
@@ "Flow_05gqmpv" :> "DIRECTP"
@@ "Flow_0ehcsg3" :> "ERRP"
@@ "Flow_03khyvp" :> "ACKP"
@@ "Flow_0guolab" :> "ACTIVATES"
@@ "Flow_1g4l0c0" :> "DIRECTS"
@@ "Flow_0m56orh" :> "DEACTIVATES"
@@ "Flow_15a2gh1" :> "ERRS"
@@ "Flow_08aidsp" :> "ACKS"


source ==
   "Flow_1c80fvc" :> "Event_0bxauwm"
@@ "Flow_1q3i58t" :> "Event_0gwjxex"
@@ "Flow_05gqmpv" :> "Activity_0id691h"
@@ "Flow_0ehcsg3" :> "Event_03je60h"
@@ "Flow_03khyvp" :> "Event_0kegwa2"
@@ "Flow_0guolab" :> "Event_14i96pr"
@@ "Flow_1g4l0c0" :> "Activity_0byesng"
@@ "Flow_0m56orh" :> "Event_0vgg0ba"
@@ "Flow_15a2gh1" :> "Event_0r02vo3"
@@ "Flow_08aidsp" :> "Event_0oj4f06"
@@ "Flow_01xnorx" :> "Event_1ac2z2i"
@@ "Flow_12fakd2" :> "Gateway_1ub2ltv"
@@ "Flow_1rbt7hr" :> "Gateway_1ub2ltv"
@@ "Flow_10ytow4" :> "Gateway_0ki8tki"
@@ "Flow_0p2qd4k" :> "Activity_0xuomcr"
@@ "Flow_0q0qopg" :> "Activity_0m6r7aa"
@@ "Flow_1maux1g" :> "StartEvent_1"
@@ "Flow_0ep8hv4" :> "Event_0bxauwm"
@@ "Flow_1wf4er6" :> "Event_1et46oa"
@@ "Flow_10neqt1" :> "Gateway_0qgs992"
@@ "Flow_04ffiyw" :> "Gateway_0qgs992"
@@ "Flow_0qdi3sr" :> "Activity_0id691h"
@@ "Flow_1mj2hsk" :> "Gateway_0wl6a1o"
@@ "Flow_07deyd6" :> "Gateway_0wl6a1o"
@@ "Flow_0gh7btl" :> "Event_1pwlc9i"
@@ "Flow_00b7crz" :> "Gateway_0ok6126"
@@ "Flow_0lbxlpn" :> "Event_0gwjxex"
@@ "Flow_0g038fl" :> "Event_1agw4ay"
@@ "Flow_0p1txzr" :> "Event_14i96pr"
@@ "Flow_1pb2ee9" :> "Event_1os5ssu"
@@ "Flow_143f8dn" :> "Gateway_1m7b2rp"
@@ "Flow_104cjar" :> "Gateway_1m7b2rp"
@@ "Flow_1sf54qd" :> "Activity_0byesng"
@@ "Flow_1qn4k7o" :> "Gateway_1isams0"
@@ "Flow_0mxan7e" :> "Gateway_1isams0"
@@ "Flow_0d4ra5x" :> "Event_164f6ag"
@@ "Flow_14e42wb" :> "Gateway_0ehzoat"
@@ "Flow_1p21xfx" :> "Event_0vgg0ba"
@@ "Flow_0i8hiam" :> "Event_1matb53"
@@ "Flow_14hbae4" :> "Activity_0c5l85e"
@@ "Flow_1n1ra56" :> "Event_13r5sdw"
@@ "Flow_0qbvxf7" :> "Activity_0c215j4"
@@ "Flow_1skh2ra" :> "Gateway_0nq1hkt"
@@ "Flow_1wczndj" :> "Gateway_0nq1hkt"
@@ "Flow_0drx7uh" :> "Activity_00galsb"
@@ "Flow_0ik7oa8" :> "Activity_04y084u"
@@ "Flow_1alj9in" :> "Activity_0jootbn"
@@ "Flow_0q7wp3m" :> "Gateway_0nml6ij"
@@ "Flow_0l3fimu" :> "Gateway_0nml6ij"
@@ "Flow_1rsrumf" :> "Event_03je60h"
@@ "Flow_0owe6ra" :> "Event_0syt2y2"
@@ "Flow_1p7v2y8" :> "Gateway_1xyjdit"
@@ "Flow_12jkr8q" :> "Gateway_0hg0uq5"
@@ "Flow_17fyu56" :> "Activity_1xs44yy"
@@ "Flow_1alyuap" :> "Activity_01kew4w"
@@ "Flow_0099ioz" :> "Event_0kegwa2"
@@ "Flow_0wycw1f" :> "Event_1900qpj"
@@ "Flow_1fb9j2l" :> "Activity_08iyx19"
@@ "Flow_002vf6t" :> "Event_10886de"
@@ "Flow_1io6s2v" :> "Activity_0x9tdqh"
@@ "Flow_0jot9v9" :> "Gateway_0y1d8f6"
@@ "Flow_11tz16c" :> "Gateway_0y1d8f6"
@@ "Flow_1nsyl9j" :> "Activity_0plaha5"
@@ "Flow_0x8186j" :> "Activity_0ioiiue"
@@ "Flow_0a37bd8" :> "Event_0oj4f06"
@@ "Flow_1rxk6wy" :> "Activity_196ygfc"
@@ "Flow_0gir2eb" :> "Activity_03ue3iv"
@@ "Flow_14t1xp3" :> "Gateway_0q68aki"
@@ "Flow_0oeg7jv" :> "Gateway_08a4yuy"
@@ "Flow_11u1vn6" :> "Event_0kujun6"
@@ "Flow_0jh8c89" :> "Event_0r02vo3"
@@ "Flow_0y7com1" :> "Gateway_11qodf7"
@@ "Flow_15sulbd" :> "Gateway_11qodf7"
@@ "Flow_0qhwa2b" :> "Activity_1qnb9i2"

target ==
   "Flow_1c80fvc" :> "Event_1matb53"
@@ "Flow_1q3i58t" :> "Event_13r5sdw"
@@ "Flow_05gqmpv" :> "Activity_0jootbn"
@@ "Flow_0ehcsg3" :> "Event_1pwlc9i"
@@ "Flow_03khyvp" :> "Event_1et46oa"
@@ "Flow_0guolab" :> "Event_1900qpj"
@@ "Flow_1g4l0c0" :> "Activity_1qnb9i2"
@@ "Flow_0m56orh" :> "Event_10886de"
@@ "Flow_15a2gh1" :> "Event_164f6ag"
@@ "Flow_08aidsp" :> "Event_1os5ssu"
@@ "Flow_01xnorx" :> "Gateway_1ub2ltv"
@@ "Flow_12fakd2" :> "Activity_0xuomcr"
@@ "Flow_1rbt7hr" :> "Activity_0m6r7aa"
@@ "Flow_10ytow4" :> "Event_1bkshv0"
@@ "Flow_0p2qd4k" :> "Gateway_0ki8tki"
@@ "Flow_0q0qopg" :> "Gateway_0ki8tki"
@@ "Flow_1maux1g" :> "Event_0bxauwm"
@@ "Flow_0ep8hv4" :> "Gateway_0qgs992"
@@ "Flow_1wf4er6" :> "Gateway_0qgs992"
@@ "Flow_10neqt1" :> "Activity_0id691h"
@@ "Flow_04ffiyw" :> "Gateway_0ok6126"
@@ "Flow_0qdi3sr" :> "Gateway_0wl6a1o"
@@ "Flow_1mj2hsk" :> "Event_1pwlc9i"
@@ "Flow_07deyd6" :> "Event_1et46oa"
@@ "Flow_0gh7btl" :> "Gateway_0ok6126"
@@ "Flow_00b7crz" :> "Event_0gwjxex"
@@ "Flow_0lbxlpn" :> "Event_1i5je9n"
@@ "Flow_0g038fl" :> "Event_14i96pr"
@@ "Flow_0p1txzr" :> "Gateway_1m7b2rp"
@@ "Flow_1pb2ee9" :> "Gateway_1m7b2rp"
@@ "Flow_143f8dn" :> "Activity_0byesng"
@@ "Flow_104cjar" :> "Gateway_0ehzoat"
@@ "Flow_1sf54qd" :> "Gateway_1isams0"
@@ "Flow_1qn4k7o" :> "Event_164f6ag"
@@ "Flow_0mxan7e" :> "Event_1os5ssu"
@@ "Flow_0d4ra5x" :> "Gateway_0ehzoat"
@@ "Flow_14e42wb" :> "Event_0vgg0ba"
@@ "Flow_1p21xfx" :> "Event_0ze20ps"
@@ "Flow_0i8hiam" :> "Activity_0c5l85e"
@@ "Flow_14hbae4" :> "Activity_1jcadcm"
@@ "Flow_1n1ra56" :> "Gateway_0nq1hkt"
@@ "Flow_0qbvxf7" :> "Event_1k7stxl"
@@ "Flow_1skh2ra" :> "Activity_00galsb"
@@ "Flow_1wczndj" :> "Activity_04y084u"
@@ "Flow_0drx7uh" :> "Activity_0c215j4"
@@ "Flow_0ik7oa8" :> "Event_0ci0tt9"
@@ "Flow_1alj9in" :> "Gateway_0nml6ij"
@@ "Flow_0q7wp3m" :> "Activity_1xs44yy"
@@ "Flow_0l3fimu" :> "Event_03je60h"
@@ "Flow_1rsrumf" :> "Gateway_0hg0uq5"
@@ "Flow_0owe6ra" :> "Gateway_1xyjdit"
@@ "Flow_1p7v2y8" :> "Activity_0jootbn"
@@ "Flow_12jkr8q" :> "Gateway_1xyjdit"
@@ "Flow_17fyu56" :> "Activity_01kew4w"
@@ "Flow_1alyuap" :> "Event_0kegwa2"
@@ "Flow_0099ioz" :> "Gateway_0hg0uq5"
@@ "Flow_0wycw1f" :> "Activity_08iyx19"
@@ "Flow_1fb9j2l" :> "Activity_1bln3fh"
@@ "Flow_002vf6t" :> "Gateway_0y1d8f6"
@@ "Flow_1io6s2v" :> "Event_04no4fg"
@@ "Flow_0jot9v9" :> "Activity_0plaha5"
@@ "Flow_11tz16c" :> "Activity_0ioiiue"
@@ "Flow_1nsyl9j" :> "Activity_0x9tdqh"
@@ "Flow_0x8186j" :> "Event_03mrlm4"
@@ "Flow_0a37bd8" :> "Gateway_0q68aki"
@@ "Flow_1rxk6wy" :> "Event_0oj4f06"
@@ "Flow_0gir2eb" :> "Activity_196ygfc"
@@ "Flow_14t1xp3" :> "Gateway_08a4yuy"
@@ "Flow_0oeg7jv" :> "Activity_1qnb9i2"
@@ "Flow_11u1vn6" :> "Gateway_08a4yuy"
@@ "Flow_0jh8c89" :> "Gateway_0q68aki"
@@ "Flow_0y7com1" :> "Event_0r02vo3"
@@ "Flow_15sulbd" :> "Activity_03ue3iv"
@@ "Flow_0qhwa2b" :> "Gateway_11qodf7"

CatN ==
   "ControllerId" :> Process
@@ "PlanterId" :> Process
@@ "SprayerId" :> Process
@@ "Event_1ac2z2i" :> NoneStartEvent
@@ "Gateway_1ub2ltv" :> Parallel
@@ "Activity_0xuomcr" :> SubProcess
@@ "Activity_0m6r7aa" :> SubProcess
@@ "Event_1bkshv0" :> NoneEndEvent
@@ "Gateway_0ki8tki" :> Parallel
@@ "StartEvent_1" :> NoneStartEvent
@@ "Event_0bxauwm" :> ThrowMessageIntermediateEvent
@@ "Gateway_0qgs992" :> ExclusiveOr
@@ "Activity_0id691h" :> SendTask
@@ "Gateway_0wl6a1o" :> EventBased
@@ "Event_1et46oa" :> CatchMessageIntermediateEvent
@@ "Event_1pwlc9i" :> CatchMessageIntermediateEvent
@@ "Gateway_0ok6126" :> ExclusiveOr
@@ "Event_0gwjxex" :> ThrowMessageIntermediateEvent
@@ "Event_1i5je9n" :> NoneEndEvent
@@ "Event_1agw4ay" :> NoneStartEvent
@@ "Event_14i96pr" :> ThrowMessageIntermediateEvent
@@ "Gateway_1m7b2rp" :> ExclusiveOr
@@ "Activity_0byesng" :> SendTask
@@ "Gateway_1isams0" :> EventBased
@@ "Event_1os5ssu" :> CatchMessageIntermediateEvent
@@ "Event_164f6ag" :> CatchMessageIntermediateEvent
@@ "Gateway_0ehzoat" :> ExclusiveOr
@@ "Event_0vgg0ba" :> ThrowMessageIntermediateEvent
@@ "Event_0ze20ps" :> NoneEndEvent
@@ "Event_1matb53" :> MessageStartEvent
@@ "Activity_0c5l85e" :> AbstractTask
@@ "Activity_1jcadcm" :> SubProcess
@@ "Event_1k7stxl" :> NoneEndEvent
@@ "Gateway_0nq1hkt" :> ExclusiveOr
@@ "Activity_04y084u" :> AbstractTask
@@ "Event_0ci0tt9" :> NoneEndEvent
@@ "Activity_00galsb" :> AbstractTask
@@ "Activity_0c215j4" :> AbstractTask
@@ "Event_13r5sdw" :> MessageBoundaryEvent
@@ "Event_0syt2y2" :> NoneStartEvent
@@ "Activity_0jootbn" :> ReceiveTask
@@ "Gateway_0nml6ij" :> ExclusiveOr
@@ "Event_03je60h" :> ThrowMessageIntermediateEvent
@@ "Event_0kegwa2" :> ThrowMessageIntermediateEvent
@@ "Gateway_0hg0uq5" :> ExclusiveOr
@@ "Gateway_1xyjdit" :> ExclusiveOr
@@ "Activity_1xs44yy" :> AbstractTask
@@ "Activity_01kew4w" :> AbstractTask
@@ "Event_1900qpj" :> MessageStartEvent
@@ "Activity_08iyx19" :> AbstractTask
@@ "Event_04no4fg" :> NoneEndEvent
@@ "Gateway_0y1d8f6" :> ExclusiveOr
@@ "Activity_0ioiiue" :> AbstractTask
@@ "Event_03mrlm4" :> NoneEndEvent
@@ "Activity_0plaha5" :> AbstractTask
@@ "Activity_0x9tdqh" :> AbstractTask
@@ "Activity_1bln3fh" :> SubProcess
@@ "Event_10886de" :> MessageBoundaryEvent
@@ "Event_0kujun6" :> NoneStartEvent
@@ "Activity_1qnb9i2" :> ReceiveTask
@@ "Gateway_11qodf7" :> ExclusiveOr
@@ "Event_0r02vo3" :> ThrowMessageIntermediateEvent
@@ "Event_0oj4f06" :> ThrowMessageIntermediateEvent
@@ "Gateway_0q68aki" :> ExclusiveOr
@@ "Gateway_08a4yuy" :> ExclusiveOr
@@ "Activity_03ue3iv" :> AbstractTask
@@ "Activity_196ygfc" :> AbstractTask

CatE ==
   "Flow_1c80fvc" :> MessageFlow
@@ "Flow_1q3i58t" :> MessageFlow
@@ "Flow_05gqmpv" :> MessageFlow
@@ "Flow_0ehcsg3" :> MessageFlow
@@ "Flow_03khyvp" :> MessageFlow
@@ "Flow_0guolab" :> MessageFlow
@@ "Flow_1g4l0c0" :> MessageFlow
@@ "Flow_0m56orh" :> MessageFlow
@@ "Flow_15a2gh1" :> MessageFlow
@@ "Flow_08aidsp" :> MessageFlow
@@ "Flow_01xnorx" :> NormalSeqFlow
@@ "Flow_12fakd2" :> NormalSeqFlow
@@ "Flow_1rbt7hr" :> NormalSeqFlow
@@ "Flow_10ytow4" :> NormalSeqFlow
@@ "Flow_0p2qd4k" :> NormalSeqFlow
@@ "Flow_0q0qopg" :> NormalSeqFlow
@@ "Flow_1maux1g" :> NormalSeqFlow
@@ "Flow_0ep8hv4" :> NormalSeqFlow
@@ "Flow_1wf4er6" :> NormalSeqFlow
@@ "Flow_10neqt1" :> ConditionalSeqFlow
@@ "Flow_04ffiyw" :> DefaultSeqFlow
@@ "Flow_0qdi3sr" :> NormalSeqFlow
@@ "Flow_1mj2hsk" :> NormalSeqFlow
@@ "Flow_07deyd6" :> NormalSeqFlow
@@ "Flow_0gh7btl" :> NormalSeqFlow
@@ "Flow_00b7crz" :> NormalSeqFlow
@@ "Flow_0lbxlpn" :> NormalSeqFlow
@@ "Flow_0g038fl" :> NormalSeqFlow
@@ "Flow_0p1txzr" :> NormalSeqFlow
@@ "Flow_1pb2ee9" :> NormalSeqFlow
@@ "Flow_143f8dn" :> ConditionalSeqFlow
@@ "Flow_104cjar" :> DefaultSeqFlow
@@ "Flow_1sf54qd" :> NormalSeqFlow
@@ "Flow_1qn4k7o" :> NormalSeqFlow
@@ "Flow_0mxan7e" :> NormalSeqFlow
@@ "Flow_0d4ra5x" :> NormalSeqFlow
@@ "Flow_14e42wb" :> NormalSeqFlow
@@ "Flow_1p21xfx" :> NormalSeqFlow
@@ "Flow_0i8hiam" :> NormalSeqFlow
@@ "Flow_14hbae4" :> NormalSeqFlow
@@ "Flow_1n1ra56" :> NormalSeqFlow
@@ "Flow_0qbvxf7" :> NormalSeqFlow
@@ "Flow_1skh2ra" :> ConditionalSeqFlow
@@ "Flow_1wczndj" :> DefaultSeqFlow
@@ "Flow_0drx7uh" :> NormalSeqFlow
@@ "Flow_0ik7oa8" :> NormalSeqFlow
@@ "Flow_1alj9in" :> NormalSeqFlow
@@ "Flow_0q7wp3m" :> ConditionalSeqFlow
@@ "Flow_0l3fimu" :> DefaultSeqFlow
@@ "Flow_1rsrumf" :> NormalSeqFlow
@@ "Flow_0owe6ra" :> NormalSeqFlow
@@ "Flow_1p7v2y8" :> NormalSeqFlow
@@ "Flow_12jkr8q" :> NormalSeqFlow
@@ "Flow_17fyu56" :> NormalSeqFlow
@@ "Flow_1alyuap" :> NormalSeqFlow
@@ "Flow_0099ioz" :> NormalSeqFlow
@@ "Flow_0wycw1f" :> NormalSeqFlow
@@ "Flow_1fb9j2l" :> NormalSeqFlow
@@ "Flow_002vf6t" :> NormalSeqFlow
@@ "Flow_1io6s2v" :> NormalSeqFlow
@@ "Flow_0jot9v9" :> ConditionalSeqFlow
@@ "Flow_11tz16c" :> DefaultSeqFlow
@@ "Flow_1nsyl9j" :> NormalSeqFlow
@@ "Flow_0x8186j" :> NormalSeqFlow
@@ "Flow_0a37bd8" :> NormalSeqFlow
@@ "Flow_1rxk6wy" :> NormalSeqFlow
@@ "Flow_0gir2eb" :> NormalSeqFlow
@@ "Flow_14t1xp3" :> NormalSeqFlow
@@ "Flow_0oeg7jv" :> NormalSeqFlow
@@ "Flow_11u1vn6" :> NormalSeqFlow
@@ "Flow_0jh8c89" :> NormalSeqFlow
@@ "Flow_0y7com1" :> DefaultSeqFlow
@@ "Flow_15sulbd" :> ConditionalSeqFlow
@@ "Flow_0qhwa2b" :> NormalSeqFlow

LOCAL preEdges ==
  [ i \in {} |-> {}]
PreEdges(n,e) == preEdges[n,e]

PreNodes(n,e) == { target[ee] : ee \in preEdges[n,e] }
          \union { nn \in { source[ee] : ee \in preEdges[n,e] } : CatN[nn] \in { NoneStartEvent, MessageStartEvent } }

BoundaryEvent ==
   "Event_13r5sdw" :> [ attachedTo |-> "Activity_1jcadcm", cancelActivity |-> TRUE ]
@@ "Event_10886de" :> [ attachedTo |-> "Activity_1bln3fh", cancelActivity |-> TRUE ]

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

