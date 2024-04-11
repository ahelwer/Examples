--------------------------- MODULE MCFindHighest ----------------------------
EXTENDS FindHighest

CONSTANTS MaxLength, MaxNat
ASSUME MaxLength ∈ ℕ
ASSUME MaxNat ∈ ℕ

MCConstraint ≜ Len(f) ≤ MaxLength
MCNat ≜ 0‥MaxNat
MCSeq(S) ≜ UNION {[1‥n → S] : n ∈ ℕ}

=============================================================================
