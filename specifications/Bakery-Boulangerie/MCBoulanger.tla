--------------------------- MODULE MCBoulanger ------------------------------
EXTENDS Boulanger
CONSTANT MaxNat
ASSUME MaxNat ∈ ℕ
NatOverride ≜ 0 ‥ MaxNat
StateConstraint ≜ ∀ process ∈ Procs : num[process] < MaxNat
=============================================================================
