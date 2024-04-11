---------------------------- MODULE BNFGrammars -----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
-----------------------------------------------------------------------------
OneOf(s) ≜ {⟨s[i]⟩ : i ∈ DOMAIN s}
tok(s) ≜ {⟨s⟩}
Tok(S) ≜ {⟨s⟩ : s ∈ S}
-----------------------------------------------------------------------------
Nil ≜ {⟨ ⟩}
  
L & M   ≜ {s ∘ t : s ∈ L, t ∈ M}
  
L | M   ≜ L ∪ M

L⁺ ≜ 
  LET LL[n ∈ ℕ] ≜ IF n = 0 THEN L 
                                ELSE LL[n-1] | (LL[n-1] & L)

  IN  UNION {LL[n] : n ∈ ℕ}
  
L^* ≜ Nil | L⁺ 
-----------------------------------------------------------------------------
L ⩴ M ≜ L = M

Grammar ≜ [STRING → SUBSET Seq(STRING)]

LeastGrammar(P(_)) ≜
  CHOOSE G ∈ Grammar : ∧ P(G) 
                       ∧ ∀ H ∈ Grammar :
                              P(H) ⇒ ∀ s ∈ STRING : G[s] ⊆ H[s]
=============================================================================