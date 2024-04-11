------------------------------- MODULE Bags ---------------------------------
LOCAL INSTANCE Naturals

IsABag(B) ≜  B ∈ [DOMAIN B → {n ∈ ℕ : n > 0}]

BagToSet(B) ≜ DOMAIN B

SetToBag(S) ≜ [e ∈ S ↦ 1]  
  
BagIn(e,B) ≜ e ∈ BagToSet(B)

EmptyBag ≜ SetToBag({})

CopiesIn(e, B) ≜  IF BagIn(e, B) THEN B[e] ELSE 0

B1 ⊕ B2  ≜  
  [e ∈ (DOMAIN B1) ∪ (DOMAIN B2) ↦ CopiesIn(e, B1) + CopiesIn(e, B2)]
  
B1 ⊖ B2  ≜ 
  LET B ≜ [e ∈ DOMAIN B1 ↦ CopiesIn(e, B1) - CopiesIn(e, B2)]
  IN  [e ∈ {d ∈ DOMAIN B : B[d] > 0} ↦ B[e]]

LOCAL Sum(f) ≜
  LET DSum[S ∈ SUBSET DOMAIN f] ≜ LET elt ≜ CHOOSE e ∈ S : TRUE
                                     IN  IF S = {} 
                                           THEN 0
                                           ELSE f[elt] + DSum[S \ {elt}]
  IN  DSum[DOMAIN f]

BagUnion(S) ≜
  [e ∈ UNION {BagToSet(B) : B ∈ S} ↦ Sum([B ∈ S ↦ CopiesIn(e,B)])]

B1 ⊑ B2  ≜  ∧ (DOMAIN B1) ⊆ (DOMAIN B2)
            ∧ ∀ e ∈ DOMAIN B1 : B1[e] ≤ B2[e]

SubBag(B) ≜
  LET AllBagsOfSubset ≜ 
        UNION {[SB → {n ∈ ℕ : n > 0}] : SB ∈ SUBSET BagToSet(B)}  
  IN  {SB ∈ AllBagsOfSubset : ∀ e ∈ DOMAIN SB : SB[e] ≤ B[e]}

BagOfAll(F(_), B) ≜
  [e ∈ {F(d) : d ∈ BagToSet(B)} ↦ 
     Sum( [d ∈ BagToSet(B) ↦ IF F(d) = e THEN B[d] ELSE 0] ) ]

BagCardinality(B) ≜ Sum(B)
=============================================================================