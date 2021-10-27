open PWSSemantics
open PWSSyntax
open PWSProp

one sig command extends Message {}

one sig goods extends Message {}

one sig invoice extends Message {}


one sig Supplier_ extends Process {} {contains = sStart + sShipCommand + sSendInvoice + sReceiveCommand + sInvoiceManagement + sPrepareCommand + sEnd + sPar1 + sPar2
}

one sig Client_ extends Process {} {contains = cStart + cSendCommand + cEnd + cReceiveInvoice + cReceiveGoods + cStoreRequest
}

one sig sStart extends NoneStartEvent {} {}

one sig sShipCommand extends SendTask {} {}

one sig sSendInvoice extends SendTask {} {}

one sig sReceiveCommand extends ReceiveTask {} {}

one sig sInvoiceManagement extends AbstractTask {} {}

one sig sPrepareCommand extends AbstractTask {} {}

one sig sEnd extends NoneEndEvent {} {}

one sig sPar1 extends Parallel {} {}

one sig sPar2 extends Parallel {} {}

one sig cStart extends NoneStartEvent {} {}

one sig cSendCommand extends SendTask {} {}

one sig cEnd extends NoneEndEvent {} {}

one sig cReceiveInvoice extends ReceiveTask {} {}

one sig cReceiveGoods extends ReceiveTask {} {}

one sig cStoreRequest extends AbstractTask {} {}


one sig mf1 extends MessageFlow {} {source = cSendCommand
target = sReceiveCommand

message = command
}

one sig mf3 extends MessageFlow {} {source = sShipCommand
target = cReceiveGoods

message = goods
}

one sig mf2 extends MessageFlow {} {source = sSendInvoice
target = cReceiveInvoice

message = invoice
}

one sig sE1 extends NormalSequentialFlow {} {source = sStart
target = sReceiveCommand
}

one sig sE2 extends NormalSequentialFlow {} {source = sReceiveCommand
target = sPar1
}

one sig sE3 extends NormalSequentialFlow {} {source = sPar1
target = sPrepareCommand
}

one sig sE4 extends NormalSequentialFlow {} {source = sPar1
target = sInvoiceManagement
}

one sig sE5 extends NormalSequentialFlow {} {source = sPrepareCommand
target = sPar2
}

one sig sE6 extends NormalSequentialFlow {} {source = sInvoiceManagement
target = sPar2
}

one sig sE7 extends NormalSequentialFlow {} {source = sPar2
target = sShipCommand
}

one sig sE8 extends NormalSequentialFlow {} {source = sShipCommand
target = sSendInvoice
}

one sig sE9 extends NormalSequentialFlow {} {source = sSendInvoice
target = sEnd
}

one sig cE1 extends NormalSequentialFlow {} {source = cStart
target = cSendCommand
}

one sig cE2 extends NormalSequentialFlow {} {source = cSendCommand
target = cStoreRequest
}

one sig cE3 extends NormalSequentialFlow {} {source = cStoreRequest
target = cReceiveInvoice
}

one sig cE4 extends NormalSequentialFlow {} {source = cReceiveInvoice
target = cReceiveGoods
}

one sig cE5 extends NormalSequentialFlow {} {source = cReceiveGoods
target = cEnd
}

check {Safe} for 0 but 15 State

check {SimpleTermination} for 0 but 24 State

//check {CorrectTermination} for 0 but 25 State

//check {CorrectTermination} for 0 but 9 State

//check {EmptyNetTermination} for 0 but 25 State

//run {Safe} for 0 but 11 State


