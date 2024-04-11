---------------------- MODULE SyncTerminationDetection ----------------------
(***************************************************************************)
(* An abstract specification of the termination detection problem in a     *)
(* ring with synchronous communication.                                    *)
(***************************************************************************)
EXTENDS Naturals
CONSTANT N
ASSUME NAssumption ≜ N ∈ ℕ \ {0}

Node ≜ 0 ‥ N-1

VARIABLES 
  active,               \* activation status of nodes
  terminationDetected   \* has termination been detected?

TypeOK ≜
  ∧ active ∈ [Node → BOOLEAN]
  ∧ terminationDetected ∈ BOOLEAN

terminated ≜ ∀ n ∈ Node : ¬ active[n]

(***************************************************************************)
(* Initial condition: the nodes can be active or inactive, termination     *)
(* may (but need not) be detected immediately if all nodes are inactive.   *)
(***************************************************************************)
Init ≜
  ∧ active ∈ [Node → BOOLEAN]
  ∧ terminationDetected ∈ {FALSE, terminated}

Terminate(i) ≜  \* node i terminates
  ∧ active[i]
  ∧ active' = [active EXCEPT ![i] = FALSE]
     (* possibly (but not necessarily) detect termination if all nodes are inactive *)
  ∧ terminationDetected' ∈ {terminationDetected, terminated'}

Wakeup(i,j) ≜  \* node i activates node j
  ∧ active[i]
  ∧ active' = [active EXCEPT ![j] = TRUE]
  ∧ UNCHANGED terminationDetected

DetectTermination ≜
  ∧ terminated
  ∧ terminationDetected' = TRUE
  ∧ UNCHANGED active

Next ≜
  ∨ ∃ i ∈ Node : Terminate(i)
  ∨ ∃ i,j ∈ Node : Wakeup(i,j)
  ∨ DetectTermination

vars ≜ ⟨active, terminationDetected⟩
Spec ≜ Init ∧ □[Next]_vars ∧ WF_vars(DetectTermination)

Stable ≜ □(terminationDetected ⇒ □terminated)

Live ≜ terminated ↝ terminationDetected

=============================================================================
\* Modification History
\* Last modified Thu Jan 21 16:08:09 CET 2021 by merz
\* Created Sun Jan 10 15:19:20 CET 2021 by merz