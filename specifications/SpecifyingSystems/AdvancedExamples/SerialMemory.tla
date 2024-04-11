-------------------------- MODULE SerialMemory --------------------------
EXTENDS RegisterInterface

Inner(InitMem, opQ, opOrder) ≜ INSTANCE InnerSerial

Spec ≜ ∃ InitMem ∈ [Adr → Val] : 
           \EE opQ, opOrder : Inner(InitMem, opQ, opOrder)!Spec
=============================================================================