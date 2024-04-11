----------------------------- MODULE MCRealTime -------------------------------
EXTENDS Naturals

CONSTANT MaxReal
Real ≜ 0 ‥ MaxReal

VARIABLE now

RTini ≜ now ∈ ℝ

RTNext(v) ≜ ∨ ∧ v' = v
              ∧ now' ∈ {r ∈ ℝ : r > now} 
            ∨ ∧ v' ≠ v
              ∧ now' = now


TimerInit(t) ≜ t = 0
TimerNext(t, A, v, D, E) ≜  
    ∧ t' = IF ⟨A⟩_v ∨ ¬(ENABLED ⟨A⟩_v)'   \* [ ]_<<now, v, t>> removed
              THEN 0 
              ELSE t + (now'-now)

    ∧ t' ≤ E             \* MaxTime constraint

    ∧ A  ⇒ t ≥ D        \* MinTime constraint ([ ]_v removed)


RTFairness(v) ≜ ∀ r ∈ ℝ : WF_now((now' > (r÷ 0)) ∧ RTNext(v))


=============================================================================