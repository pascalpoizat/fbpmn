---------------- MODULE e037Comm ----------------

EXTENDS TLC, PWSTypes

VARIABLES nodemarks, edgemarks, net

Interest ==
  "Airline_" :> { "order" }
  @@ "Customer_" :> { "offer", "confirmation", "payment confirmation" }
  @@ "TravelAgency_" :> { "travel", "payment", "rejection" }

ContainRel ==
  "Airline_" :> { "Ticket_Order_Received", "Handle_Payment", "Was_Payment_Made", "Payment_Confirmed", "Payment_Refused", "Confirm_Payment" }
  @@ "Customer_" :> { "StartEvent_1", "Check_Offer", "Is_the_Offer_Interesting", "Reject_Offer", "Book_Travel", "Offer_Rejected", "Pay_Travel", "Booking_Confirmed", "Payment_Confirmation_Received", "Travel_Paid" }
  @@ "TravelAgency_" :> { "Offer_Cancelled", "Offer_Rejection_Received", "Status_Waiting", "Make_Travel_Offer", "Offer_Needed", "Ticket_Ordered", "Order_Ticket", "IntermediateThrowEvent_0kagqq2", "Confirm_Booking", "Booking_Received" }

Node == { "Customer_", "TravelAgency_", "Airline_", "StartEvent_1", "Check_Offer", "Is_the_Offer_Interesting", "Reject_Offer", "Book_Travel", "Offer_Rejected", "Pay_Travel", "Booking_Confirmed", "Payment_Confirmation_Received", "Travel_Paid", "Offer_Cancelled", "Offer_Rejection_Received", "Status_Waiting", "Make_Travel_Offer", "Offer_Needed", "Ticket_Ordered", "Order_Ticket", "IntermediateThrowEvent_0kagqq2", "Confirm_Booking", "Booking_Received", "Ticket_Order_Received", "Handle_Payment", "Was_Payment_Made", "Payment_Confirmed", "Payment_Refused", "Confirm_Payment" }

Edge == { "MessageFlow_1j3ru8z", "MessageFlow_01l3u25", "MessageFlow_0jtu5yc", "MessageFlow_1p97q31", "MessageFlow_0y2wjrm", "MessageFlow_08bo5ej", "MessageFlow_15n7wk4", "SequenceFlow_037u61c", "SequenceFlow_0dfevt9", "Offer_is_not_Interesting", "Offer_is_Interesting", "SequenceFlow_1qo309k", "SequenceFlow_1y19v10", "SequenceFlow_1p9f9nn", "SequenceFlow_0rbkpuc", "SequenceFlow_1fm8n43", "SequenceFlow_1b9yiqz", "SequenceFlow_10id4f8", "SequenceFlow_1wbphor", "SequenceFlow_1l28um0", "SequenceFlow_02xdetn", "SequenceFlow_06mgtsm", "SequenceFlow_0wyug2s", "SequenceFlow_1bhdal8", "SequenceFlow_1bxiri7", "SequenceFlow_09iuwhk", "SequenceFlow_1ybfy8r", "Payment_Was_Made", "Payment_Was_Not_Made", "SequenceFlow_1di11xa" }

Message == { "order", "offer", "travel", "rejection", "payment", "confirmation", "payment confirmation" }

msgtype ==
   "MessageFlow_1j3ru8z" :> "order"
@@ "MessageFlow_01l3u25" :> "offer"
@@ "MessageFlow_0jtu5yc" :> "travel"
@@ "MessageFlow_1p97q31" :> "rejection"
@@ "MessageFlow_0y2wjrm" :> "payment"
@@ "MessageFlow_08bo5ej" :> "confirmation"
@@ "MessageFlow_15n7wk4" :> "payment confirmation"


source ==
   "MessageFlow_1j3ru8z" :> "Order_Ticket"
@@ "MessageFlow_01l3u25" :> "Make_Travel_Offer"
@@ "MessageFlow_0jtu5yc" :> "Book_Travel"
@@ "MessageFlow_1p97q31" :> "Reject_Offer"
@@ "MessageFlow_0y2wjrm" :> "Pay_Travel"
@@ "MessageFlow_08bo5ej" :> "Confirm_Booking"
@@ "MessageFlow_15n7wk4" :> "Confirm_Payment"
@@ "SequenceFlow_037u61c" :> "StartEvent_1"
@@ "SequenceFlow_0dfevt9" :> "Check_Offer"
@@ "Offer_is_not_Interesting" :> "Is_the_Offer_Interesting"
@@ "Offer_is_Interesting" :> "Is_the_Offer_Interesting"
@@ "SequenceFlow_1qo309k" :> "Reject_Offer"
@@ "SequenceFlow_1y19v10" :> "Book_Travel"
@@ "SequenceFlow_1p9f9nn" :> "Booking_Confirmed"
@@ "SequenceFlow_0rbkpuc" :> "Pay_Travel"
@@ "SequenceFlow_1fm8n43" :> "Payment_Confirmation_Received"
@@ "SequenceFlow_1b9yiqz" :> "Order_Ticket"
@@ "SequenceFlow_10id4f8" :> "IntermediateThrowEvent_0kagqq2"
@@ "SequenceFlow_1wbphor" :> "Confirm_Booking"
@@ "SequenceFlow_1l28um0" :> "Booking_Received"
@@ "SequenceFlow_02xdetn" :> "Offer_Rejection_Received"
@@ "SequenceFlow_06mgtsm" :> "Status_Waiting"
@@ "SequenceFlow_0wyug2s" :> "Status_Waiting"
@@ "SequenceFlow_1bhdal8" :> "Make_Travel_Offer"
@@ "SequenceFlow_1bxiri7" :> "Offer_Needed"
@@ "SequenceFlow_09iuwhk" :> "Ticket_Order_Received"
@@ "SequenceFlow_1ybfy8r" :> "Handle_Payment"
@@ "Payment_Was_Made" :> "Was_Payment_Made"
@@ "Payment_Was_Not_Made" :> "Was_Payment_Made"
@@ "SequenceFlow_1di11xa" :> "Confirm_Payment"

target ==
   "MessageFlow_1j3ru8z" :> "Ticket_Order_Received"
@@ "MessageFlow_01l3u25" :> "StartEvent_1"
@@ "MessageFlow_0jtu5yc" :> "Booking_Received"
@@ "MessageFlow_1p97q31" :> "Offer_Rejection_Received"
@@ "MessageFlow_0y2wjrm" :> "IntermediateThrowEvent_0kagqq2"
@@ "MessageFlow_08bo5ej" :> "Booking_Confirmed"
@@ "MessageFlow_15n7wk4" :> "Payment_Confirmation_Received"
@@ "SequenceFlow_037u61c" :> "Check_Offer"
@@ "SequenceFlow_0dfevt9" :> "Is_the_Offer_Interesting"
@@ "Offer_is_not_Interesting" :> "Reject_Offer"
@@ "Offer_is_Interesting" :> "Book_Travel"
@@ "SequenceFlow_1qo309k" :> "Offer_Rejected"
@@ "SequenceFlow_1y19v10" :> "Booking_Confirmed"
@@ "SequenceFlow_1p9f9nn" :> "Pay_Travel"
@@ "SequenceFlow_0rbkpuc" :> "Payment_Confirmation_Received"
@@ "SequenceFlow_1fm8n43" :> "Travel_Paid"
@@ "SequenceFlow_1b9yiqz" :> "Ticket_Ordered"
@@ "SequenceFlow_10id4f8" :> "Order_Ticket"
@@ "SequenceFlow_1wbphor" :> "IntermediateThrowEvent_0kagqq2"
@@ "SequenceFlow_1l28um0" :> "Confirm_Booking"
@@ "SequenceFlow_02xdetn" :> "Offer_Cancelled"
@@ "SequenceFlow_06mgtsm" :> "Offer_Rejection_Received"
@@ "SequenceFlow_0wyug2s" :> "Booking_Received"
@@ "SequenceFlow_1bhdal8" :> "Status_Waiting"
@@ "SequenceFlow_1bxiri7" :> "Make_Travel_Offer"
@@ "SequenceFlow_09iuwhk" :> "Handle_Payment"
@@ "SequenceFlow_1ybfy8r" :> "Was_Payment_Made"
@@ "Payment_Was_Made" :> "Confirm_Payment"
@@ "Payment_Was_Not_Made" :> "Payment_Refused"
@@ "SequenceFlow_1di11xa" :> "Payment_Confirmed"

CatN ==
   "Customer_" :> Process
@@ "TravelAgency_" :> Process
@@ "Airline_" :> Process
@@ "StartEvent_1" :> MessageStartEvent
@@ "Check_Offer" :> AbstractTask
@@ "Is_the_Offer_Interesting" :> ExclusiveOr
@@ "Reject_Offer" :> SendTask
@@ "Book_Travel" :> SendTask
@@ "Offer_Rejected" :> NoneEndEvent
@@ "Pay_Travel" :> SendTask
@@ "Booking_Confirmed" :> CatchMessageIntermediateEvent
@@ "Payment_Confirmation_Received" :> CatchMessageIntermediateEvent
@@ "Travel_Paid" :> NoneEndEvent
@@ "Offer_Cancelled" :> NoneEndEvent
@@ "Offer_Rejection_Received" :> CatchMessageIntermediateEvent
@@ "Status_Waiting" :> EventBased
@@ "Make_Travel_Offer" :> SendTask
@@ "Offer_Needed" :> NoneStartEvent
@@ "Ticket_Ordered" :> NoneEndEvent
@@ "Order_Ticket" :> SendTask
@@ "IntermediateThrowEvent_0kagqq2" :> CatchMessageIntermediateEvent
@@ "Confirm_Booking" :> SendTask
@@ "Booking_Received" :> CatchMessageIntermediateEvent
@@ "Ticket_Order_Received" :> MessageStartEvent
@@ "Handle_Payment" :> AbstractTask
@@ "Was_Payment_Made" :> ExclusiveOr
@@ "Payment_Confirmed" :> NoneEndEvent
@@ "Payment_Refused" :> NoneEndEvent
@@ "Confirm_Payment" :> SendTask

CatE ==
   "MessageFlow_1j3ru8z" :> MessageFlow
@@ "MessageFlow_01l3u25" :> MessageFlow
@@ "MessageFlow_0jtu5yc" :> MessageFlow
@@ "MessageFlow_1p97q31" :> MessageFlow
@@ "MessageFlow_0y2wjrm" :> MessageFlow
@@ "MessageFlow_08bo5ej" :> MessageFlow
@@ "MessageFlow_15n7wk4" :> MessageFlow
@@ "SequenceFlow_037u61c" :> NormalSeqFlow
@@ "SequenceFlow_0dfevt9" :> NormalSeqFlow
@@ "Offer_is_not_Interesting" :> NormalSeqFlow
@@ "Offer_is_Interesting" :> NormalSeqFlow
@@ "SequenceFlow_1qo309k" :> NormalSeqFlow
@@ "SequenceFlow_1y19v10" :> NormalSeqFlow
@@ "SequenceFlow_1p9f9nn" :> NormalSeqFlow
@@ "SequenceFlow_0rbkpuc" :> NormalSeqFlow
@@ "SequenceFlow_1fm8n43" :> NormalSeqFlow
@@ "SequenceFlow_1b9yiqz" :> NormalSeqFlow
@@ "SequenceFlow_10id4f8" :> NormalSeqFlow
@@ "SequenceFlow_1wbphor" :> NormalSeqFlow
@@ "SequenceFlow_1l28um0" :> NormalSeqFlow
@@ "SequenceFlow_02xdetn" :> NormalSeqFlow
@@ "SequenceFlow_06mgtsm" :> NormalSeqFlow
@@ "SequenceFlow_0wyug2s" :> NormalSeqFlow
@@ "SequenceFlow_1bhdal8" :> NormalSeqFlow
@@ "SequenceFlow_1bxiri7" :> NormalSeqFlow
@@ "SequenceFlow_09iuwhk" :> NormalSeqFlow
@@ "SequenceFlow_1ybfy8r" :> NormalSeqFlow
@@ "Payment_Was_Made" :> NormalSeqFlow
@@ "Payment_Was_Not_Made" :> NormalSeqFlow
@@ "SequenceFlow_1di11xa" :> NormalSeqFlow

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

