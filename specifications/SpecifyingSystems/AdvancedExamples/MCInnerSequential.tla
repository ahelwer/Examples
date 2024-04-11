--------------------- MODULE MCInnerSequential -----------------------
EXTENDS InnerSequential

CONSTANT MaxQLen
Constraint ≜ ∀ p ∈ Proc : Len(opQ[p]) ≤ MaxQLen

AlwaysResponds ≜ 
  (*************************************************************************)
  (* A simple liveness property, implied by the fact that every request    *)
  (* eventually generates a response.                                      *)
  (*************************************************************************)
  ∀ p ∈ Proc, r ∈ Reg :
       (regFile[p][r].op ≠ "Free") ↝ (regFile[p][r].op = "Free")
=============================================================================
