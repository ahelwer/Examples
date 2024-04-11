
------------------------- MODULE MCRealTimeHourClock --------------------------
EXTENDS Naturals, HourClock 
VARIABLE now 
CONSTANT Rho, MaxReal, SecondsPerHour
-----------------------------------------------------------------------------

Real ≜ 0 ‥ MaxReal

ASSUME (Rho ∈ ℝ) ∧  (Rho > 0) 

   VARIABLE t  
   TNext ≜ t' = IF HCnxt THEN 0 ELSE t+(now'-now) 
   IsTimer ≜ (t = 0)  ∧  □[TNext]_⟨t,hr,now⟩
   MaxTime ≜ □(t ≤  SecondsPerHour + Rho)  
   MinTime ≜ □[HCnxt ⇒ t ≥ SecondsPerHour - Rho]_hr
   HCTime ≜ IsTimer ∧ MaxTime ∧ MinTime 


NowNext ≜ ∧ now' ∈ {r ∈ ℝ : r > now} 
          ∧ UNCHANGED hr  

BigNext ≜ ∧ [NowNext]_now
          ∧ [HCnxt]_hr
          ∧ TNext
          ∧ HCnxt ⇒ t ≥ SecondsPerHour - Rho
          ∧ t' ≤  SecondsPerHour + Rho

BigInit ≜ ∧ HCini
          ∧ t = 0
          ∧ now ∈ ℝ 

Fairness ≜ ∀ r ∈ ℝ : WF_now(NowNext ∧ (now'>r))

NonZeno ≜ ∀ r ∈ ℝ : ◇(now ≥ r)

ImpliedTemporal ≜ ∀ h ∈ 1‥12 : □◇(hr = h)

RT ≜ ∧ now ∈ ℝ 
     ∧ □[NowNext]_now
     ∧ ∀ r ∈ ℝ : WF_now(NowNext ∧ (now'>r))

ErrorTemporal ≜ □((now ≠ 4) ⇒ ◇□(now ≠ 4))
=============================================================================
 