---------------------- MODULE Finitize_ReplicatedLog ------------------------

EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction, Divergence

VARIABLES log, executed, converge

vars ≜ ⟨log, executed, converge⟩

S ≜ INSTANCE ReplicatedLog

TypeOK ≜
  ∧ log ∈ Seq(Transaction)
  ∧ Len(log) ≤ Divergence
  ∧ executed ∈ [Node → 0 ‥ Divergence]

Liveness ≜ converge ↝ S!Convergence

Init ≜
  ∧ S!Init
  ∧ converge = FALSE

WriteTx(n, tx) ≜
  ∧ ¬converge
  ∧ Len(log) < Divergence
  ∧ S!WriteTx(n, tx)
  ∧ UNCHANGED converge

ExecuteTx(n) ≜
  ∧ S!ExecuteTx(n)
  ∧ UNCHANGED converge

GarbageCollect ≜
  LET SetMin(s) ≜ CHOOSE e ∈ s : ∀ o ∈ s : e ≤ o IN
  LET MinExecuted ≜ SetMin({executed[o] : o ∈ Node}) IN
  ∧ log' = [i ∈ 1 ‥ Len(log) - MinExecuted ↦ log[i + MinExecuted]]
  ∧ executed' = [n ∈ Node ↦ executed[n] - MinExecuted]
  ∧ UNCHANGED converge

Converge ≜
  ∧ converge' = TRUE
  ∧ UNCHANGED ⟨log, executed⟩

Fairness ≜ ∀ n ∈ Node : WF_vars(ExecuteTx(n))

Next ≜
  ∨ ∃ n ∈ Node : ∃ tx ∈ Transaction : WriteTx(n, tx)
  ∨ ∃ n ∈ Node : ExecuteTx(n)
  ∨ GarbageCollect
  ∨ Converge

Spec ≜
  ∧ Init
  ∧ □[Next]_vars
  ∧ Fairness

=============================================================================
