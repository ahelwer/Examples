-------------------------- MODULE CigaretteSmokers --------------------------
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME ∧ Offers ⊆ (SUBSET Ingredients)
       ∧ ∀ n ∈ Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a BOOLEAN flag signifying smoker's state         *)
(* (smoking/not smoking)                                                   *)
(* 'dealer' is an element of 'Offers', or an empty set                     *)
(***************************************************************************)
TypeOK ≜ ∧ smokers ∈ [Ingredients → [smoking: BOOLEAN]]
         ∧ dealer  ∈ Offers ∨ dealer = {}
          
vars ≜ ⟨smokers, dealer⟩

ChooseOne(S, P(_)) ≜ CHOOSE x ∈ S : P(x) ∧ ∀ y ∈ S : P(y) ⇒ y = x

Init ≜ ∧ smokers = [r ∈ Ingredients ↦ [smoking ↦ FALSE]]
       ∧ dealer ∈ Offers
        
startSmoking ≜ ∧ dealer ≠ {}
               ∧ smokers' = [r ∈ Ingredients ↦ [smoking ↦ {r} ∪ 
                                                      dealer = Ingredients]]
               ∧ dealer' = {}
                
stopSmoking ≜ ∧ dealer = {}
              ∧ LET r ≜ ChooseOne(Ingredients,
                                     LAMBDA x : smokers[x].smoking)
                  IN smokers' = [smokers EXCEPT ![r].smoking = FALSE] 
              ∧ dealer' ∈ Offers

Next ≜ startSmoking ∨ stopSmoking

Spec ≜ Init ∧ □[Next]_vars
FairSpec ≜ Spec ∧ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment                                                                  *)
(***************************************************************************)
AtMostOne ≜ Cardinality({r ∈ Ingredients : smokers[r].smoking}) ≤ 1
=============================================================================