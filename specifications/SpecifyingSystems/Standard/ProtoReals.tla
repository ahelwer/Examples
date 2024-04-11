----------------------------- MODULE ProtoReals ----------------------------- 
EXTENDS Peano

IsModelOfReals(R, Plus, Times, Leq) ≜ 
  LET IsAbelianGroup(G, Id, _+_) ≜ 
        ∧ Id ∈ G
        ∧ ∀ a, b ∈ G : a + b ∈ G
        ∧ ∀ a ∈ G : Id + a = a
        ∧ ∀ a, b, c ∈ G : (a + b) + c = a + (b + c)
        ∧ ∀ a ∈ G : ∃ minusa ∈ G : a + minusa = Id
        ∧ ∀ a, b ∈ G : a + b = b + a
     (**********************************************************************)
     (* Plus and Times are functions and Leq is a set, but it's more       *)
     (* convenient to turn them into the infix operators +, *, and \leq    *)
     (**********************************************************************)
      a + b    ≜ Plus[a, b]
      a * b    ≜ Times[a, b]
      a ≤ b ≜ ⟨a, b⟩ ∈ Leq
  IN  ∧ ℕ ⊆ R
      ∧ ∀ n ∈ ℕ : Succ[n] = n + Succ[Zero]
      ∧ IsAbelianGroup(R, Zero, +)
      ∧ IsAbelianGroup(R \ {Zero}, Succ[Zero], *)
      ∧ ∀ a, b, c ∈ R : a * (b + c) = (a * b) + (a * c) 
      ∧ ∀ a, b ∈ R : ∧ (a ≤ b) ∨ (b ≤ a)
                     ∧ (a ≤ b) ∧ (b ≤ a) ⇔ (a = b)
      ∧ ∀ a, b, c ∈ R : ∧ (a ≤ b) ∧ (b ≤ c) ⇒ (a ≤ c)
                        ∧ (a ≤ b) ⇒ 
                                 ∧ (a + c) ≤ (b + c)
                                 ∧ (Zero ≤ c) ⇒ (a * c) ≤ (b * c)
      ∧ ∀ S ∈ SUBSET R :
           LET SBound(a) ≜ ∀ s ∈ S : s ≤ a
           IN  (∃ a ∈ R : SBound(a)) ⇒ 
                  (∃ sup ∈ R : ∧ SBound(sup) 
                               ∧ ∀ a ∈ R : SBound(a) ⇒ (sup≤ a))

THEOREM ∃ R, Plus, Times, Leq : IsModelOfReals(R, Plus, Times, Leq)
-----------------------------------------------------------------------------
RM ≜ CHOOSE RM : IsModelOfReals(RM.R, RM.Plus, RM.Times, RM.Leq)

Real  ≜ RM.R
-----------------------------------------------------------------------------
Infinity ≜ CHOOSE x : x ∉ ℝ
MinusInfinity ≜ CHOOSE x : x ∉ ℝ ∪ {Infinity}

a + b ≜ RM.Plus[a, b]

a * b ≜ RM.Times[a, b]

a ≤ b ≜ CASE (a ∈ ℝ) ∧ (b ∈ ℝ) → ⟨a, b⟩ ∈ RM.Leq
              □ (a = Infinity) ∧ (b ∈ ℝ ∪ {MinusInfinity})  → FALSE
              □ (a ∈ ℝ  ∪ {MinusInfinity}) ∧ (b = Infinity) → TRUE
              □ (a = b) → TRUE

a - b ≜ CASE (a ∈ ℝ) ∧ (b ∈ ℝ)  → CHOOSE c ∈ ℝ : c + b = a
           □ (a ∈ ℝ) ∧ (b = Infinity)      → MinusInfinity
           □ (a ∈ ℝ) ∧ (b = MinusInfinity) → Infinity 

a / b ≜ CHOOSE c ∈ ℝ : a = b * c

Int  ≜ ℕ ∪ {Zero - n : n ∈ ℕ}
-----------------------------------------------------------------------------
a ^ b ≜ 
  LET RPos ≜ {r ∈ ℝ \ {Zero} : Zero ≤ r}
      exp  ≜ CHOOSE f ∈ [(RPos × ℝ) ∪ (ℝ × RPos) 
                                   ∪ ((ℝ \ {Zero}) × ℤ) → ℝ] :
               ∧ ∀ r ∈ ℝ :
                    ∧ f[r, Succ[Zero]] = r
                    ∧ ∀ m, n ∈ ℤ : (r ≠ Zero) ⇒ 
                                           (f[r, m+n] = f[r, m] * f[r, n])
               ∧ ∀ r ∈ RPos :
                    ∧ f[Zero, r] = Zero
                    ∧ ∀ s, t ∈ ℝ : f[r, s*t] = f[f[r, s], t]
                    ∧ ∀ s, t ∈ RPos : (s ≤ t) ⇒ (f[r,s] ≤ f[r,t])
  IN  exp[a, b]
=============================================================================

