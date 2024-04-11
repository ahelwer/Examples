----------------------------- MODULE Relation ------------------------------
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                            *)
(***************************************************************************)

(***************************************************************************)
(* Is the relation R reflexive over S?                                     *)
(***************************************************************************)
IsReflexive(R, S) ≜ ∀ x ∈ S : R[x,x]

(***************************************************************************)
(* Is the relation R irreflexive over set S?                               *)
(***************************************************************************)
IsIrreflexive(R, S) ≜ ∀ x ∈ S : ¬ R[x,x]

(***************************************************************************)
(* Is the relation R symmetric over set S?                                 *)
(***************************************************************************)
IsSymmetric(R, S) ≜ ∀ x,y ∈ S : R[x,y] ⇔ R[y,x]

(***************************************************************************)
(* Is the relation R asymmetric over set S?                                *)
(***************************************************************************)
IsAsymmetric(R, S) ≜ ∀ x,y ∈ S : ¬(R[x,y] ∧ R[y,x])

(***************************************************************************)
(* Is the relation R transitive over set S?                                *)
(***************************************************************************)
IsTransitive(R, S) ≜ ∀ x,y,z ∈ S : R[x,y] ∧ R[y,z] ⇒ R[x,z]

(***************************************************************************)
(* Compute the transitive closure of relation R over set S.                *)
(***************************************************************************)
TransitiveClosure(R, S) ≜
  LET N ≜ Cardinality(S)
      trcl[n ∈ ℕ] ≜ 
          [x,y ∈ S ↦ IF n=0 THEN R[x,y]
                         ELSE ∨ trcl[n-1][x,y]
                              ∨ ∃ z ∈ S : trcl[n-1][x,z] ∧ trcl[n-1][z,y]]
  IN  trcl[N]

(***************************************************************************)
(* Compute the reflexive transitive closure of relation R over set S.      *)
(***************************************************************************)
ReflexiveTransitiveClosure(R, S) ≜
  LET trcl ≜ TransitiveClosure(R,S)
  IN  [x,y ∈ S ↦ x=y ∨ trcl[x,y]]

(***************************************************************************)
(* Is the relation R connected over set S, i.e. does there exist a path    *)
(* between two arbitrary elements of S?                                    *)
(***************************************************************************)
IsConnected(R, S) ≜
  LET rtrcl ≜ ReflexiveTransitiveClosure(R,S)
  IN  ∀ x,y ∈ S : rtrcl[x,y]

=============================================================================
\* Modification History
\* Last modified Sun Jun 14 15:32:47 CEST 2020 by merz
\* Created Tue Apr 26 10:24:07 CEST 2016 by merz