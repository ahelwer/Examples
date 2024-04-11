---- MODULE MCReachabilityTest ----
EXTENDS ReachabilityTest, Sequences

CONSTANT RandomSuccCount

RandomSuccSet ≜ SuccSet2(RandomSuccCount)

ASSUME ∀ i ∈ DOMAIN Test : Test[i]

LimitedSeq(S) ≜ UNION {
  [1 ‥ len → S]
  : len ∈ 0 ‥ Cardinality(Nodes)
}
===================================
