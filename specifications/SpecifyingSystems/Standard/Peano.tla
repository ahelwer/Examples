------------------------------- MODULE Peano -------------------------------
PeanoAxioms(N, Z, Sc) ≜ 
  ∧ Z ∈ N
  ∧ Sc ∈ [N → N]
  ∧ ∀ n ∈ N : (∃ m ∈ N : n = Sc[m]) ⇔ (n ≠ Z)
  ∧ ∀ S ∈ SUBSET N : (Z ∈ S) ∧ (∀ n ∈ S : Sc[n] ∈ S) ⇒ (S = N)

ASSUME ∃ N, Z, Sc : PeanoAxioms(N, Z, Sc)

Succ ≜ CHOOSE Sc : ∃ N, Z : PeanoAxioms(N, Z, Sc)
Nat  ≜ DOMAIN Succ
Zero ≜ CHOOSE Z : PeanoAxioms(ℕ, Z, Succ)
=============================================================================