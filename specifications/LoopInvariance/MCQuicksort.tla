---------------------------- MODULE MCQuicksort -----------------------------
EXTENDS Quicksort
CONSTANT MaxSeqLen
ASSUME MaxSeqLen ∈ ℕ
LimitedSeq(S) ≜ UNION {[1 ‥ n → S] : n ∈ 1 ‥ MaxSeqLen}
=============================================================================
