--------------------------- MODULE Finitize_CRDT ----------------------------

EXTENDS Naturals

CONSTANTS Node, Divergence

VARIABLES counter, converge

vars ≜ ⟨counter, converge⟩

S ≜ INSTANCE CRDT

TypeOK ≜
  ∧ S!TypeOK
  ∧ counter ∈ [Node → [Node → 0 ‥ Divergence]]
  ∧ converge ∈ BOOLEAN

Safety ≜ S!Safety

Monotonicity ≜ □[
  ∨ S!Monotonic
  ∨ ∀ a, b, c, d ∈ Node :
    (counter'[a][b] - counter[a][b]) = (counter'[c][d] - counter[c][d])
]_vars

Liveness ≜ converge ↝ S!Convergence

Init ≜
  ∧ S!Init
  ∧ converge = FALSE

Increment(n) ≜
  ∧ ¬converge
  ∧ counter[n][n] < Divergence
  ∧ S!Increment(n)
  ∧ UNCHANGED converge

Gossip(n, o) ≜
  ∧ S!Gossip(n, o)
  ∧ UNCHANGED converge

Converge ≜
  ∧ converge' = TRUE
  ∧ UNCHANGED counter

GarbageCollect ≜
  LET SetMin(s) ≜ CHOOSE e ∈ s : ∀ o ∈ s : e ≤ o IN
  LET Transpose ≜ SetMin({counter[n][o] : n, o ∈ Node}) IN
  ∧ counter' = [
      n ∈ Node ↦ [
        o ∈ Node ↦ counter[n][o] - Transpose
      ]
    ]
  ∧ UNCHANGED converge

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)
  ∨ Converge
  ∨ GarbageCollect

Fairness ≜ ∀ n, o ∈ Node : WF_vars(Gossip(n, o))

StateConstraint ≜ ∀ n, o ∈ Node : counter[n][o] ≤ 4

Spec ≜
  ∧ Init
  ∧ □[Next]_vars
  ∧ Fairness

=============================================================================
