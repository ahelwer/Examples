--------------------------- MODULE MCLamportMutex ---------------------------
EXTENDS LamportMutex
CONSTANT MaxNat
ASSUME MaxNat ∈ ℕ
NatOverride ≜ 0 ‥ MaxNat
=============================================================================
