------------------------------- MODULE CRDT ---------------------------------

EXTENDS Naturals

CONSTANT Node

VARIABLE counter

TypeOK ≜ counter ∈ [Node → [Node → ℕ]]

Safety ≜ ∀ n, o ∈ Node : counter[n][n] ≥ counter[o][n]

Monotonic ≜ ∀ n, o ∈ Node : counter'[n][o] ≥ counter[n][o]

Monotonicity ≜ □[Monotonic]_counter

Convergence ≜ ∀ n, o ∈ Node : counter[n] = counter[o]

Init ≜ counter = [n ∈ Node ↦ [o ∈ Node ↦ 0]]

Increment(n) ≜ counter' = [counter EXCEPT ![n][n] = @ + 1]

Gossip(n, o) ≜
  LET Max(a, b) ≜ IF a > b THEN a ELSE b IN
  counter' = [
    counter EXCEPT ![o] = [
      nodeView ∈ Node ↦
        Max(counter[n][nodeView], counter[o][nodeView])
      ]
    ]

Next ≜
  ∨ ∃ n ∈ Node : Increment(n)
  ∨ ∃ n, o ∈ Node : Gossip(n, o)

Spec ≜
  ∧ Init
  ∧ □[Next]_counter

=============================================================================
