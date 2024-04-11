-------------------------- MODULE ReadersWriters --------------------------
(***************************************************************************)
(* This solution to the readers-writers problem, cf.                       *)
(* https://en.wikipedia.org/wiki/Readers–writers_problem,                  *)
(* uses a queue in order to fairly serve all requests.                     *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars ≜ ⟨readers, writers, waiting⟩

Actors ≜ 1‥NumActors

ToSet(s) ≜ { s[i] : i ∈ DOMAIN s }

read(s)  ≜ s[1] = "read"
write(s) ≜ s[1] = "write"

WaitingToRead  ≜ { p[2] : p ∈ ToSet(SelectSeq(waiting, read)) }

WaitingToWrite ≜ { p[2] : p ∈ ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

TryRead(actor) ≜
    ∧ actor ∉ WaitingToRead
    ∧ waiting' = Append(waiting, ⟨"read", actor⟩)
    ∧ UNCHANGED ⟨readers, writers⟩

TryWrite(actor) ≜
    ∧ actor ∉ WaitingToWrite
    ∧ waiting' = Append(waiting, ⟨"write", actor⟩)
    ∧ UNCHANGED ⟨readers, writers⟩

Read(actor) ≜
    ∧ readers' = readers ∪ {actor}
    ∧ waiting' = Tail(waiting)
    ∧ UNCHANGED writers

Write(actor) ≜
    ∧ readers = {}
    ∧ writers' = writers ∪ {actor}
    ∧ waiting' = Tail(waiting)
    ∧ UNCHANGED readers

ReadOrWrite ≜
    ∧ waiting ≠ ⟨⟩
    ∧ writers = {}
    ∧ LET pair  ≜ Head(waiting)
           actor ≜ pair[2]
       IN CASE pair[1] = "read" → Read(actor)
            □ pair[1] = "write" → Write(actor)

StopActivity(actor) ≜
    IF actor ∈ readers
    THEN ∧ readers' = readers \ {actor}
         ∧ UNCHANGED ⟨writers, waiting⟩
    ELSE ∧ writers' = writers \ {actor}
         ∧ UNCHANGED ⟨readers, waiting⟩

Stop ≜ ∃ actor ∈ readers ∪ writers : StopActivity(actor)

---------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Init ≜
    ∧ readers = {}
    ∧ writers = {}
    ∧ waiting = ⟨⟩

Next ≜
    ∨ ∃ actor ∈ Actors : TryRead(actor)
    ∨ ∃ actor ∈ Actors : TryWrite(actor)
    ∨ ReadOrWrite
    ∨ Stop

Fairness ≜
    ∧ ∀ actor ∈ Actors : WF_vars(TryRead(actor))
    ∧ ∀ actor ∈ Actors : WF_vars(TryWrite(actor))
    ∧ WF_vars(ReadOrWrite)
    ∧ WF_vars(Stop)

Spec ≜ Init ∧ □[Next]_vars ∧ Fairness

---------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

TypeOK ≜
    ∧ readers ⊆ Actors
    ∧ writers ⊆ Actors
    ∧ waiting ∈ Seq({"read", "write"} × Actors)

Safety ≜
    ∧ ¬(readers ≠ {} ∧ writers ≠ {})
    ∧ Cardinality(writers) ≤ 1

(**************)
(* Properties *)
(**************)

Liveness ≜
    ∧ ∀ actor ∈ Actors : □◇(actor ∈ readers)
    ∧ ∀ actor ∈ Actors : □◇(actor ∈ writers)
    ∧ ∀ actor ∈ Actors : □◇(actor ∉ readers)
    ∧ ∀ actor ∈ Actors : □◇(actor ∉ writers)

============================================================================