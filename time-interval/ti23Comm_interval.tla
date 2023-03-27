---------------- MODULE ti23Comm_interval ----------------
EXTENDS ti23Comm
Interval == INSTANCE PWSIntervals
Prop == []Interval!Before("Book_Travel","Order_Ticket")
================================================================
