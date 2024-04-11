------------------------------- MODULE TCommit ------------------------------
CONSTANT RM       \* The set of participating resource managers
VARIABLE rmState  \* `rmState[rm]' is the state of resource manager rm.
-----------------------------------------------------------------------------
TCTypeOK ≜ 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState ∈ [RM → {"working", "prepared", "committed", "aborted"}]

TCInit ≜   rmState = [rm ∈ RM ↦ "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit ≜ ∀ rm ∈ RM : rmState[rm] ∈ {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted ≜ ∀ rm ∈ RM : rmState[rm] ≠ "committed" 
  (*************************************************************************)
  (* True iff neither no resource manager has decided to commit.           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the actions that may be performed by the RMs, and then    *)
(* define the complete next-state action of the specification to be the    *)
(* disjunction of the possible RM actions.                                 *)
(***************************************************************************)
Prepare(rm) ≜ ∧ rmState[rm] = "working"
              ∧ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm)  ≜ ∨ ∧ rmState[rm] = "prepared"
                ∧ canCommit
                ∧ rmState' = [rmState EXCEPT ![rm] = "committed"]
              ∨ ∧ rmState[rm] ∈ {"working", "prepared"}
                ∧ notCommitted
                ∧ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext ≜ ∃ rm ∈ RM : Prepare(rm) ∨ Decide(rm)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCSpec ≜ TCInit ∧ □[TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol.                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now assert invariance properties of the specification.               *)
(***************************************************************************)
TCConsistent ≜  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  ∀ rm1, rm2 ∈ RM : ¬ ∧ rmState[rm1] = "aborted"
                      ∧ rmState[rm2] = "committed"

THEOREM TCSpec ⇒ □(TCTypeOK ∧ TCConsistent)
  (*************************************************************************)
  (* Asserts that TCTypeOK and TCConsistent are invariants of the protocol. *)
  (*************************************************************************)
=============================================================================