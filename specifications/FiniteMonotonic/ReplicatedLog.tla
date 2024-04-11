--------------------------- MODULE ReplicatedLog ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Node, Transaction

VARIABLES log, executed

vars ≜ ⟨log, executed⟩

TypeOK ≜
  ∧ log ∈ Seq(Transaction)
  ∧ executed ∈ [Node → ℕ]

Convergence ≜ ∀ n ∈ Node : executed[n] = Len(log)

Init ≜
  ∧ log = ⟨⟩
  ∧ executed = [n ∈ Node ↦ 0]

WriteTx(n, tx) ≜
  ∧ executed[n] = Len(log)
  ∧ log' = Append(log, tx)
  ∧ executed' = [executed EXCEPT ![n] = @ + 1]

ExecuteTx(n) ≜
  ∧ executed[n] < Len(log)
  ∧ executed' = [executed EXCEPT ![n] = @ + 1]
  ∧ UNCHANGED log

Next ≜
  ∨ ∃ n ∈ Node : ∃ tx ∈ Transaction: WriteTx(n, tx)
  ∨ ∃ n ∈ Node : ExecuteTx(n)

Spec ≜
  ∧ Init
  ∧ □[Next]_vars

=============================================================================
