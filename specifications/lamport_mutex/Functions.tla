------------------------------ MODULE Functions -----------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Notions about functions including injection, surjection, and bijection.*)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* Restriction of a function to a set (should be a subset of the domain).  *)
(***************************************************************************)
Restrict(f,S) ≜ [ x ∈ S ↦ f[x] ]

(***************************************************************************)
(* Range of a function.                                                    *)
(* Note: The image of a set under function f can be defined as             *)
(*       Range(Restrict(f,S)).                                             *)
(***************************************************************************)
Range(f) ≜ { f[x] : x ∈ DOMAIN f }


(***************************************************************************)
(* The inverse of a function.                                              *)
(***************************************************************************)
Inverse(f,S,T) ≜ [t ∈ T ↦ CHOOSE s ∈ S : t ∈ Range(f) ⇒ f[s] = t]


(***************************************************************************)
(* A map is an injection iff each element in the domain maps to a distinct *)
(* element in the range.                                                   *)
(***************************************************************************)
Injection(S,T) ≜ { M ∈ [S → T] : ∀ a,b ∈ S : M[a] = M[b] ⇒ a = b }


(***************************************************************************)
(* A map is a surjection iff for each element in the range there is some   *)
(* element in the domain that maps to it.                                  *)
(***************************************************************************)
Surjection(S,T) ≜ { M ∈ [S → T] : ∀ t ∈ T : ∃ s ∈ S : M[s] = t }


(***************************************************************************)
(* A map is a bijection iff it is both an injection and a surjection.      *)
(***************************************************************************)
Bijection(S,T) ≜ Injection(S,T) ∩ Surjection(S,T)


(***************************************************************************)
(* An injection, surjection, or bijection exists if the corresponding set  *)
(* is nonempty.                                                            *)
(***************************************************************************)
ExistsInjection(S,T)  ≜ Injection(S,T) ≠ {}
ExistsSurjection(S,T) ≜ Surjection(S,T) ≠ {}
ExistsBijection(S,T)  ≜ Bijection(S,T) ≠ {}


=============================================================================
\* Modification History
\* Last modified Wed Jul 10 20:32:37 CEST 2013 by merz
\* Last modified Wed Jun 05 12:14:19 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:35 PDT 2013 by tomr
\* Created Thu Apr 11 10:30:48 PDT 2013 by tomr