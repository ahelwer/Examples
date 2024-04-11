----------------------- MODULE DifferentialEquations ------------------------
LOCAL INSTANCE Reals
LOCAL INSTANCE Sequences
LOCAL PosReal ≜ {r ∈ ℝ : r > 0}
LOCAL OpenInterval(a, b) ≜ {s ∈ ℝ : a < s ∧ s < b}
LOCAL Nbhd(r,e) ≜  OpenInterval(r-e, r+e)
LOCAL IsFirstDeriv(df, f) ≜
        ∧ df ∈ [DOMAIN f → ℝ]
        ∧ ∀ r ∈ DOMAIN f : 
              ∀ e ∈ PosReal :
                 ∃ d ∈ PosReal : 
                    ∀ s ∈ Nbhd(r,d) \ {r} :
                        (f[s] - f[r])/(s - r) ∈ Nbhd(df[r], e)

LOCAL IsDeriv(n, df, f) ≜ 
  LET IsD[k ∈ 0‥n,  g ∈ [DOMAIN f → ℝ]] ≜
         IF k = 0 
           THEN g = f
           ELSE ∃ gg ∈ [DOMAIN f → ℝ] : ∧ IsFirstDeriv(g, gg)
                                        ∧ IsD[k-1, gg]
  IN  IsD[n, df]

Integrate(D, a, b, InitVals) ≜
  LET n ≜ Len(InitVals)
      gg ≜ CHOOSE g : 
              ∃ e ∈ PosReal : 
                 ∧ g ∈ [0‥n → [OpenInterval(a-e, b+e) → ℝ]]
                 ∧ ∀ i ∈ 1‥n : ∧ IsDeriv(i, g[i], g[0])
                               ∧ g[i-1][a] = InitVals[i]
                 ∧ ∀ r ∈ OpenInterval(a-e, b+e) :
                        D[ ⟨r⟩ ∘ [i ∈ 1‥(n+1) ↦ g[i-1][r]] ] = 0
  IN  [i ∈ 1‥n ↦ gg[i-1][b]]
=============================================================================


