------------------------------ MODULE SpanTreeTest ------------------------------
(***************************************************************************)
(* The specification in this module is a modified version of the one in    *)
(* module SpanTree obtained by replacing the declared constant Edges with  *)
(* a variable of the same name that is set initially to any possible set   *)
(* of edges with nodes in Nodes.  Thus, it can be used to test the         *)
(* algorithm of SpanTree on all possible graphs having a particular number *)
(* of nodes.                                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Randomization

CONSTANTS Nodes, Root, MaxCardinality

ASSUME ∧ Root ∈ Nodes
       ∧ MaxCardinality ∈ ℕ
       ∧ MaxCardinality ≥ Cardinality(Nodes)
       
VARIABLES mom, dist, Edges
vars ≜ ⟨mom, dist, Edges⟩

Nbrs(n) ≜ {m ∈ Nodes : {m, n} ∈ Edges}

TypeOK ≜ ∧ mom ∈ [Nodes → Nodes]
         ∧ dist ∈ [Nodes → ℕ]
         ∧ ∀ e ∈ Edges : (e ⊆ Nodes) ∧ (Cardinality(e) = 2)

Init ≜ ∧ mom = [n ∈ Nodes ↦ n]
       ∧ dist = [n ∈ Nodes ↦ IF n = Root THEN 0 ELSE MaxCardinality]
       ∧ Edges ∈ {E ∈ SUBSET (SUBSET Nodes) : ∀ e ∈ E : Cardinality(e) = 2}
           (****************************************************************)
           (* SUBSET S is the set of all subsets of a set S.  Thus, this   *)
           (* allows Edges to have as its initial value any set of sets of *)
           (* nodes containing exactly two nodes.                          *)
           (****************************************************************)
        
Next ≜ ∃ n ∈ Nodes :
          ∃ m ∈ Nbrs(n) : 
             ∧ dist[m] < 1 + dist[n]
             ∧ ∃ d ∈ (dist[m]+1) ‥ (dist[n] - 1) :
                    ∧ dist' = [dist EXCEPT ![n] = d]
                    ∧ mom'  = [mom  EXCEPT ![n] = m]
                    ∧ Edges' = Edges

Spec ≜ Init ∧ □[Next]_vars ∧ WF_vars(Next)
-----------------------------------------------------------------------------
PostCondition ≜ 
  ∀ n ∈ Nodes :
    ∨ ∧ n = Root 
      ∧ dist[n] = 0
      ∧ mom[n] = n
    ∨ ∧ dist[n] = MaxCardinality 
      ∧ mom[n] = n
      ∧ ∀ m ∈ Nbrs(n) : dist[m] = MaxCardinality
    ∨ ∧ dist[n] ∈ 1‥(MaxCardinality-1)
      ∧ mom[n] ∈ Nbrs(n)
      ∧ dist[n] = dist[mom[n]] + 1

Safety ≜ □((¬ ENABLED Next) ⇒ PostCondition)

Liveness ≜ ◇PostCondition
(***************************************************************************)
(* This took a few seconds to check for 4 nodes, and about 25 minutes for  *)
(* 5 nodes on my laptop.  To compute the initial value of Edges, TLC has   *)
(* to compute all the elements of SUBSET (SUBSET Nodes) (the set of all    *)
(* subsets of the set of all sets of nodes) and then throw away all the    *)
(* elements of that set that don't consist entirely of sets having         *)
(* cardinality 2.  For N nodes, SUBSET(SUBSET Nodes) contains 2^(2^N)      *)
(* elements.                                                               *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Mon Jun 17 05:43:38 PDT 2019 by lamport
\* Created Fri Jun 14 03:07:58 PDT 2019 by lamport