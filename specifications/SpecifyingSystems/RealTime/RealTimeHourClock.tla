
------------------------- MODULE RealTimeHourClock --------------------------
EXTENDS Reals, HourClock 
VARIABLE now 
CONSTANT Rho 
ASSUME (Rho ∈ ℝ) ∧  (Rho > 0) 
-----------------------------------------------------------------------------

   -------------------------- MODULE Inner ----------------------------------
   VARIABLE t  
   TNext ≜ t' = IF HCnxt THEN 0 ELSE t+(now'-now) 
   Timer   ≜ (t = 0)  ∧  □[TNext]_⟨t,hr, now⟩
   MaxTime ≜ □(t ≤  3600 + Rho)  
   MinTime ≜ □[HCnxt ⇒ t ≥ 3600 - Rho]_hr
   HCTime  ≜ Timer ∧ MaxTime ∧ MinTime 
  ==========================================================================

I(t) ≜ INSTANCE Inner 
 
NowNext ≜ ∧ now' ∈ {r ∈ ℝ : r > now} 
          ∧ UNCHANGED hr  

RTnow ≜ ∧ now ∈ ℝ 
        ∧ □[NowNext]_now 
        ∧ ∀ r ∈ ℝ : WF_now(NowNext ∧ (now'>r))

RTHC ≜ HC  ∧  RTnow ∧  (\EE t : I(t)!HCTime)
=============================================================================
 