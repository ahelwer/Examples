------------------------- MODULE NaturalsInduction -------------------------
(***************************************************************************)
(* This module contains useful theorems for inductive proofs and recursive *)
(* definitions over the naturals.                                          *)
(*                                                                         *)
(* Some of the statements of the theorems are decomposed in terms of       *)
(* definitions.  This is done for two reasons:                             *)
(*                                                                         *)
(*  - It makes it easier for the backends to instantiate the theorems      *)
(*    when those definitions are not expanded.                             *)
(*                                                                         *)
(*  - It can be convenient when writing proofs to use those definitions    *)
(*    rather than having to write out their expansions.                    *)
(*                                                                         *)
(* The proofs of these theorems appear in module NaturalsInduction\_proofs.*)
(***************************************************************************)
EXTENDS Integers, TLAPS

(***************************************************************************)
(* The following is the simple statement of inductions over the naturals.  *)
(* For predicates P defined by a moderately complex operator, it is often  *)
(* useful to hide the operator definition before using this theorem. That  *)
(* is, you first define a suitable operator P (not necessarily by that     *)
(* name), prove the two hypotheses of the theorem, and then hide the       *) 
(* definition of P when using the theorem.                                 *)
(***************************************************************************)
THEOREM NatInduction ≜ 
  ASSUME NEW P(_),
         P(0),
         ∀ n ∈ ℕ : P(n) ⇒ P(n+1)
  PROVE  ∀ n ∈ ℕ : P(n)

(***************************************************************************)
(* A useful corollary of NatInduction                                      *)
(***************************************************************************)
THEOREM DownwardNatInduction ≜ 
  ASSUME NEW P(_), NEW m ∈ ℕ, P(m),
         ∀ n ∈ 1 ‥ m : P(n) ⇒ P(n-1)
  PROVE  P(0)

(***************************************************************************)
(* The following theorem expresses a stronger induction principle,         *)
(* also known as course-of-values induction, where the induction           *)
(* hypothesis is available for all strictly smaller natural numbers.       *)
(***************************************************************************)
THEOREM GeneralNatInduction ≜
          ASSUME NEW P(_),
                 ∀ n ∈ ℕ : (∀ m ∈ 0‥(n-1) : P(m)) ⇒ P(n)
          PROVE  ∀ n ∈ ℕ : P(n)

(***************************************************************************)
(* The following theorem expresses the ``least-number principle'':         *)
(* if P(n) is true for some natural number n then there is a               *)
(* smallest natural number for which P is true. It could be derived in     *)
(* module WellFoundedInduction as a corollary of the fact that the natural *)
(* numbers are well ordered, but we give a direct proof.                   *)
(***************************************************************************)
THEOREM SmallestNatural ≜
  ASSUME NEW P(_), NEW n ∈ ℕ, P(n)
  PROVE  ∃ m ∈ ℕ : ∧ P(m)
                   ∧ ∀ k ∈ 0 ‥ m-1 : ¬ P(k)

(***************************************************************************)
(* The following theorem says that a recursively defined function f over   *)
(* the natural numbers is well-defined if for every n \in Nat the          *)
(* definition of f[n] depends only on arguments smaller than n.            *)
(***************************************************************************)
THEOREM RecursiveFcnOfNat ≜
  ASSUME NEW Def(_,_), 
         ASSUME NEW n ∈ ℕ, NEW g, NEW h,
                ∀ i ∈ 0‥(n-1) : g[i] = h[i] 
         PROVE  Def(g, n) = Def(h, n)
  PROVE  LET f[n ∈ ℕ] ≜ Def(f, n)
         IN  f = [n ∈ ℕ ↦ Def(f, n)]


(***************************************************************************)
(* The following theorem NatInductiveDef is what you use to justify a      *)
(* function defined by primitive recursion over the naturals.              *)
(***************************************************************************)
NatInductiveDefHypothesis(f, f0, Def(_,_)) ≜ 
   (f =  CHOOSE g : g = [i ∈ ℕ ↦ IF i = 0 THEN f0 ELSE Def(g[i-1], i)])
NatInductiveDefConclusion(f, f0, Def(_,_)) ≜
     f = [i ∈ ℕ ↦ IF i = 0 THEN f0 ELSE Def(f[i-1], i)]

THEOREM NatInductiveDef ≜
  ASSUME NEW Def(_,_), NEW f, NEW f0,
         NatInductiveDefHypothesis(f, f0, Def)
  PROVE  NatInductiveDefConclusion(f, f0, Def)


(***************************************************************************)
(* The following two theorems allow you to prove the type of a recursively *)
(* defined function over the natural numbers.                              *)
(***************************************************************************)
THEOREM RecursiveFcnOfNatType ≜
  ASSUME NEW f, NEW S, NEW Def(_,_), f = [n ∈ ℕ ↦ Def(f,n)],
         ASSUME NEW n ∈ ℕ, NEW g, ∀ i ∈ 0 ‥ n-1 : g[i] ∈ S
         PROVE  Def(g,n) ∈ S
  PROVE  f ∈ [ℕ → S]

THEOREM NatInductiveDefType ≜
  ASSUME NEW Def(_,_), NEW S, NEW f, NEW f0 ∈ S,
         NatInductiveDefConclusion(f, f0, Def),
         f0 ∈ S,
         ∀ v ∈ S, n ∈ ℕ \ {0} : Def(v, n) ∈ S
  PROVE  f ∈ [ℕ → S]

(***************************************************************************)
(* The following theorems show uniqueness of functions recursively defined *)
(* over Nat.                                                               *)
(***************************************************************************)
THEOREM RecursiveFcnOfNatUnique ≜
  ASSUME NEW Def(_,_), NEW f, NEW g,
         f = [n ∈ ℕ ↦ Def(f,n)],
         g = [n ∈ ℕ ↦ Def(g,n)],
         ASSUME NEW n ∈ ℕ, NEW ff, NEW gg,
                ∀ i ∈ 0‥(n-1) : ff[i] = gg[i] 
         PROVE  Def(ff, n) = Def(gg, n)
  PROVE  f = g

THEOREM NatInductiveUnique ≜ 
  ASSUME NEW Def(_,_), NEW f, NEW g, NEW f0,
         NatInductiveDefConclusion(f, f0, Def),
         NatInductiveDefConclusion(g, f0, Def)
  PROVE  f = g

(***************************************************************************)
(* The following theorems are analogous to the preceding ones but for      *)
(* functions defined over intervals of natural numbers.                    *)
(***************************************************************************)

FiniteNatInductiveDefHypothesis(f, c, Def(_,_), m, n) ≜ 
   (f =  CHOOSE g : g = [i ∈ m‥n ↦ IF i = m THEN c ELSE Def(g[i-1], i)])
FiniteNatInductiveDefConclusion(f, c, Def(_,_), m, n) ≜
     f = [i ∈ m‥n ↦ IF i = m THEN c ELSE Def(f[i-1], i)]
                                       
THEOREM FiniteNatInductiveDef ≜
  ASSUME NEW Def(_,_), NEW f, NEW c, NEW m ∈ ℕ, NEW n ∈ ℕ,
         FiniteNatInductiveDefHypothesis(f, c, Def, m, n)
  PROVE  FiniteNatInductiveDefConclusion(f, c, Def, m, n)

THEOREM FiniteNatInductiveDefType ≜
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW c ∈ S, NEW m ∈ ℕ, NEW n ∈ ℕ,
         FiniteNatInductiveDefConclusion(f, c, Def, m, n),
         ∀ v ∈ S, i ∈ (m+1) ‥ n : Def(v,i) ∈ S
  PROVE  f ∈ [m‥n → S]

THEOREM FiniteNatInductiveUnique ≜ 
  ASSUME NEW Def(_,_), NEW f, NEW g, NEW c, NEW m ∈ ℕ, NEW n ∈ ℕ,
         FiniteNatInductiveDefConclusion(f, c, Def, m, n),
         FiniteNatInductiveDefConclusion(g, c, Def, m, n)
  PROVE  f = g

=============================================================================
(***************************************************************************)
(* The following theorems are analogous to the preceding ones but for      *)
(* functions defined over intervals of natural numbers.                    *)
(***************************************************************************)

FiniteNatInductiveDefHypothesis(f, c, Def(_,_), m, n) == 
   (f =  CHOOSE g : g = [i \in m..n |-> IF i = m THEN c ELSE Def(g[i-1], i)])
FiniteNatInductiveDefConclusion(f, c, Def(_,_), m, n) ==
     f = [i \in m..n |-> IF i = m THEN c ELSE Def(f[i-1], i)]
                                       
THEOREM FiniteNatInductiveDef ==
  ASSUME NEW Def(_,_), NEW f, NEW c, NEW m \in Nat, NEW n \in Nat,
         FiniteNatInductiveDefHypothesis(f, c, Def, m, n)
  PROVE  FiniteNatInductiveDefConclusion(f, c, Def, m, n)

THEOREM FiniteNatInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW c \in S, NEW m \in Nat, NEW n \in Nat,
         FiniteNatInductiveDefConclusion(f, c, Def, m, n),
         \A v \in S, i \in (m+1) .. n : Def(v,i) \in S
  PROVE  f \in [m..n -> S]

THEOREM FiniteNatInductiveUnique == 
  ASSUME NEW Def(_,_), NEW f, NEW g, NEW c, NEW m \in Nat, NEW n \in Nat,
         FiniteNatInductiveDefConclusion(f, c, Def, m, n),
         FiniteNatInductiveDefConclusion(g, c, Def, m, n)
  PROVE  f = g

(***************************************************************************)
(* The following example shows how this module is used.                    *)
(***************************************************************************)

factorial[n \in Nat] == IF n = 0 THEN 1 ELSE n * factorial[n-1]

THEOREM FactorialDefConclusion == NatInductiveDefConclusion(factorial, 1, LAMBDA v,n : n*v)
<1>1. NatInductiveDefHypothesis(factorial, 1, LAMBDA v,n : n*v)
  BY DEF NatInductiveDefHypothesis, factorial 
<1>2. QED
  BY <1>1, NatInductiveDef

THEOREM FactorialDef == \A n \in Nat : factorial[n] = IF n = 0 THEN 1 ELSE n * factorial[n-1]
BY FactorialDefConclusion DEFS NatInductiveDefConclusion

THEOREM FactorialType == factorial \in [Nat -> Nat]
<1>1. \A v \in Nat, n \in Nat \ {0} : n * v \in Nat
  OBVIOUS
<1>2. QED
  BY <1>1, 1 \in Nat, NatInductiveDefType, FactorialDefConclusion, Isa

=============================================================================
\* Modification History
\* Last modified Thu May 08 12:29:46 CEST 2014 by merz
\* Last modified Tue Oct 15 12:06:48 CEST 2013 by shaolin
\* Last modified Sat Nov 26 08:49:59 CET 2011 by merz
\* Last modified Mon Nov 07 08:58:05 PST 2011 by lamport
\* Created Mon Oct 31 02:52:05 PDT 2011 by lamport