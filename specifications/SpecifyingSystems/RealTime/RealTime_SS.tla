----------------------------- MODULE RealTime_SS -------------------------------
EXTENDS Reals 
VARIABLE now

RTBound(A, v, D, E) ≜ 
  LET TNext(t)  ≜  t' = IF ⟨A⟩_v ∨ ¬(ENABLED ⟨A⟩_v)'
                           THEN 0 
                           ELSE t + (now'-now)

      Timer(t) ≜ (t=0)  ∧  □[TNext(t)]_⟨t, v, now⟩

      MaxTime(t) ≜ □(t ≤ E) 

      MinTime(t) ≜ □[A ⇒ t ≥ D]_v 
  IN \EE t : Timer(t) ∧ MaxTime(t) ∧ MinTime(t)
-----------------------------------------------------------------------------
RTnow(v) ≜ LET NowNext ≜ ∧ now' ∈ {r ∈ ℝ : r > now} 
                         ∧ UNCHANGED v
            IN  ∧ now ∈ ℝ 
                ∧ □[NowNext]_now
                ∧ ∀ r ∈ ℝ : WF_now(NowNext ∧ (now'>r))
=============================================================================