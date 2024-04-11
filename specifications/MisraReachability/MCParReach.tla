---- MODULE MCParReach ----
EXTENDS ParReach

ConnectedToSomeButNotAll ≜
  CHOOSE succ ∈ [Nodes → SUBSET Nodes]
  : ∀ n ∈ Nodes : Cardinality(succ[n]) = 2

LimitedSeq(S) ≜ UNION {
  [1 ‥ len → S]
  : len ∈ 0 ‥ Cardinality(Nodes)
}

============================
