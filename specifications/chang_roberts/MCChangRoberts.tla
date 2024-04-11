--------------------------- MODULE MCChangRoberts ---------------------------
EXTENDS Naturals
CONSTANT N
VARIABLES msgs, pc, initiator, state
ASSUME N ∈ ℕ
Id ≜ [i ∈ 1 ‥ N ↦ i]
INSTANCE ChangRoberts
=============================================================================
