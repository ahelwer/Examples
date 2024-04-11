--------------------------- MODULE MCInnerSerial ----------------------------
(***************************************************************************)
(* This is a module to test the InnerSerial specification.                 *)
(***************************************************************************)

EXTENDS InnerSerial \* , TLC

CONSTANT MaxQLen
    (***********************************************************************)
    (* To bound the state space, we constrain the length of opQ[p] to be   *)
    (* at most MaxQLen, for all p.                                         *)
    (***********************************************************************)

MCNat ≜ 0 ‥ MaxQLen 
  (*************************************************************************)
  (* The liveness condition contains quantification over the set           *)
  (*                                                                       *)
  (*       [proc : Proc, idx : Nat]                                        *)
  (*                                                                       *)
  (* However, it suffices that the quantification be over all possible     *)
  (* elements of opId, and hence for idx at most MaxQLen.  We therefore    *)
  (* have TLC substitute MCNat for Nat.                                    *)
  (*************************************************************************)

MCInitMem ≜ [adr ∈ Adr ↦ CHOOSE v ∈ Val  : TRUE]
  (*************************************************************************)
  (* We have to tell TLC what value to use for the constant parameter      *)
  (* InitMem.  We let it use MCInitMem, an arbitrary choice.               *)
  (*************************************************************************)
  
Constraint ≜ ∀ p ∈ Proc : Len(opQ[p]) ≤ MaxQLen
  (*************************************************************************)
  (* The constraint used to bound the size of the state space.             *)
  (*************************************************************************)
  
AlwaysResponds ≜ 
  (*************************************************************************)
  (* Some simple liveness properties, implied by the fact that every       *)
  (* request eventually generates a response.                              *)
  (*************************************************************************)
  ∧ ∀ p ∈ Proc, r ∈ Reg :
       (regFile[p][r].op ≠ "Free") ↝ (regFile[p][r].op = "Free")
  ∧ ∀ oi ∈ [proc : Proc, idx : ℕ] :
         (oi ∈ opId) ↝ (oi ∈ opId ∧ opIdQ(oi).reg = Done)

=============================================================================