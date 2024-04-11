------------------------ MODULE JointActionMemory ---------------------------
EXTENDS MemoryInterface

   -------------------- MODULE InnerEnvironmentComponent --------------------
   VARIABLE rdy
   IE  ≜ rdy = [p ∈ Proc ↦ TRUE] 

   Erqst(p) ≜ ∧ rdy[p]
              ∧ ∃ req ∈ MReq : Send(p, req,  memInt, memInt') 
              ∧ rdy' = [rdy EXCEPT ![p] = FALSE]

   ERsp(p)  ≜ ∧ ∃ rsp ∈ Val ∪ {NoVal} : 
                       Reply(p, rsp,  memInt, memInt') 
              ∧ rdy' = [rdy EXCEPT ![p] = TRUE]

   NE ≜ ∃ p ∈ Proc : Erqst(p) ∨ ERsp(p)

   IESpec ≜ IE ∧ □[NE]_⟨memInt, rdy⟩
   ==========================================================================

   ---------------------- MODULE InnerMemoryComponent -----------------------
   EXTENDS InternalMemory
   MRqst(p) ≜   ∧ ∃ req ∈ MReq : 
                      ∧ Send(p, req, memInt, memInt') 
                      ∧ buf' = [buf EXCEPT ![p] = req]
                      ∧ ctl' = [ctl EXCEPT ![p] = "busy"]
                ∧ UNCHANGED mem 

   NM ≜ ∃ p ∈ Proc : MRqst(p) ∨ Do(p) ∨ Rsp(p)

   IMSpec ≜ IInit ∧ □[NM]_⟨memInt, mem, ctl, buf⟩
   ==========================================================================

IEnv(rdy) ≜ INSTANCE InnerEnvironmentComponent

IMem(mem, ctl, buf) ≜ INSTANCE InnerMemoryComponent

Spec ≜ ∧ \EE rdy : IEnv(rdy)!IESpec  
       ∧ \EE mem, ctl, buf : IMem(mem,ctl,buf)!IMSpec
=============================================================================