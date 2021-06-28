from enum import Enum, auto


class Communication(Enum):
    Network01Bag = auto()
    Network02FifoPair = auto()
    Network03Causal = auto()
    Network04Inbox = auto()
    Network05Outbox = auto()
    Network06Fifo = auto()
    Network07RSC = auto()


class Property(Enum):
    Prop01Type = auto()
    Prop02Safe = auto()
    Prop03Sound = auto()
    Prop04MsgSound = auto()
