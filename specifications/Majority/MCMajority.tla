------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers
CONSTANTS A, B, C, bound
ASSUME bound ∈ ℕ

Value ≜ {A,B,C}
BoundedSeq(S) ≜ UNION { [1 ‥ n → S] : n ∈ 0 ‥ bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

==============================================================================