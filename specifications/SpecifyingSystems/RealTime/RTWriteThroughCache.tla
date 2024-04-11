----------------------- MODULE RTWriteThroughCache --------------------------
EXTENDS WriteThroughCache, RealTime_SS

CONSTANT N
ASSUME (N ∈ ℕ) ∧ (Proc = 0 ‥ N-1)

CONSTANTS Delta, Epsilon, Rho

ASSUME ∧ (Delta ∈ ℝ)   ∧ (Delta > 0)
       ∧ (Epsilon ∈ ℝ) ∧ (Epsilon > 0)
       ∧ (Rho ∈ ℝ)     ∧ (Rho > 0)
       ∧ 2*(N+1)*Epsilon + (N+QLen)*Delta ≤ Rho
-----------------------------------------------------------------------------
VARIABLE lastP

RTInit ≜ Init ∧ (lastP ∈ Proc)

position(p) ≜ CHOOSE i ∈ 1 ‥ N : p = (lastP + i) % N

canGoNext(p) ≜ 
   ∀ q ∈ Proc : (position(q) < position(p))
            ⇒  ¬ENABLED(RdMiss(q) ∨ DoWr(q))     

RTRdMiss(p) ≜ ∧ canGoNext(p)
              ∧ RdMiss(p) 
              ∧ lastP' = p    

RTDoWr(p)   ≜ ∧ canGoNext(p)
              ∧ DoWr(p) 
              ∧ lastP' = p    

RTNext ≜
    ∨ ∃ p∈ Proc : RTRdMiss(p) ∨ RTDoWr(p)
    ∨ ∧ ∨ ∃ p∈ Proc : ∨ Req(p) ∨ Rsp(p) ∨ DoRd(p) 
                      ∨ ∃ a ∈ Adr : Evict(p, a)
        ∨ MemQWr ∨ MemQRd    
      ∧ UNCHANGED lastP

vars ≜ ⟨memInt, wmem, buf, ctl, cache, memQ, lastP⟩

RTSpec ≜ ∧ RTInit ∧ □[RTNext]_vars
         ∧ RTBound(MemQWr ∨ MemQRd, vars, 0, Delta)
         ∧ ∀ p ∈ Proc :
                ∧ RTBound(RTDoWr(p) ∨ DoRd(p) ∨ Rsp(p),
                        vars, 0, Epsilon)
                ∧ RTBound(RTRdMiss(p), vars, 0, Epsilon)
         ∧ RTnow(vars)
-----------------------------------------------------------------------------
RTM ≜ INSTANCE RTMemory 
THEOREM RTSpec ⇒ RTM!RTSpec
=============================================================================