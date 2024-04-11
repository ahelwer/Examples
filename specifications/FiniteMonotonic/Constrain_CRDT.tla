-------------------------- MODULE Constrain_CRDT ----------------------------

EXTENDS Naturals

CONSTANT Node

VARIABLES counter, converge

vars ≜ ⟨counter, converge⟩

S ≜ INSTANCE CRDT

TypeOK ≜
  ∧ S!TypeOK
  ∧ converge ∈ BOOLEAN

Safety ≜ S!Safety

Monotonicity ≜ S!Monotonicity

Liveness ≜ converge ↝ S!Convergence

Init ≜
  ∧ S!Init
  ∧ converge = FALSE

Increment(n) ≜
  ∧ ¬converge
  ∧ S!Increment(n)
  ∧ UNCHANGED converge

Gossip(n, o) ≜
  ∧ S!Gossip(n, o)
  ∧ UNCHANGED converge

Converge ≜
  ∧ converge' = TRUE
  ∧ UNCHANGED counter

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)
  ∨ Converge

Fairness ≜ ∀ n, o ∈ Node : WF_vars(Gossip(n, o))

StateConstraint ≜ ∀ n, o ∈ Node : counter[n][o] ≤ 3

Spec ≜
  ∧ Init
  ∧ □[Next]_vars
  ∧ Fairness

=============================================================================
