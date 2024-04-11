------------------------------ MODULE Naturals ------------------------------ 
LOCAL R ≜ INSTANCE ProtoReals

Nat ≜ R!Nat

a + b ≜ R!+(a, b)
a - b ≜ R!-(a, b)
a * b ≜ R!*(a, b)
a ^ b ≜ R!^(a, b)
a ≤ b ≜ R!≤(a, b)
a ≥ b ≜ b ≤ a
a < b ≜ (a ≤ b) ∧ (a ≠ b)
a > b ≜ b < a
a ‥ b ≜ {i ∈ R!Int : (a ≤ i) ∧ (i ≤ b)}
a ÷ b ≜ CHOOSE n ∈ R!Int : ∃ r ∈ 0 ‥ (b-1) : a =  b * n + r
a % b    ≜  a  -  b * (a ÷ b)
=============================================================================