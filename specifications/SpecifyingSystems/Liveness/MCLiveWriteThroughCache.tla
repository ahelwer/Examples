----------------------- MODULE MCLiveWriteThroughCache ----------------------
(***************************************************************************)
(* This is a module used for running TLC to check the specification of the *)
(* write-through cache in module LiveWriteThroughCache.  We check that it  *)
(* implements the LiveInternalMemory specification under the refinement    *)
(* mapping described in the section "Proving Implementation" of chapter "A *)
(* Caching Memory".                                                        *)
(*                                                                         *)
(* This module is the same as module MCWriteThroughCache of the folder     *)
(* CachingMemory, except it also "instantiates" the definition of LISpec.  *)
(***************************************************************************)

EXTENDS LiveWriteThroughCache

(***************************************************************************)
(* The following definitions are substituted for the constants Send,       *)
(* Reply, and InitMemInt of the MemoryFace module.  See                    *)
(* MCInternalMemory.tla for their explanations.                            *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ≜  newMemInt = ⟨p, d⟩
MCReply(p, d, oldMemInt, newMemInt) ≜  newMemInt = ⟨p, d⟩
MCInitMemInt ≜ {⟨CHOOSE p ∈ Proc : TRUE, NoVal⟩}

(***************************************************************************)
(* As described in the section titled "Proving Implementation", the        *)
(* write-through cache specifies Spec satisfies                            *)
(*                                                                         *)
(*    Spec => LM!Inner(omem, octl, obuf)!ISpec                             *)
(*                                                                         *)
(* for the following choices of omem, octl, and obuf:                      *)
(***************************************************************************)

   omem ≜ vmem
   octl ≜ [p ∈ Proc ↦ IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
   obuf ≜ buf

(***************************************************************************)
(* If we extended what we did in the chapter "A Caching Memory" to the     *)
(* specifications with liveness, we would have a module LiveMemory that    *)
(* hides the internal variables of LiveInnerMemory, and module             *)
(* LiveWriteThroughCache would contain                                     *)
(*                                                                         *)
(*    LM == INSTANCE LiveMemory                                            *)
(*    THEOREM LSpec => LM!LSpec                                            *)
(*                                                                         *)
(* we would prove this by proving                                          *)
(*                                                                         *)
(* (1)   LSpec => LM!Inner(omem, octl, obuf)!LISpec                        *)
(*                                                                         *)
(* where Formula LM!Inner(omem, octl, obuf)!LISpec is formula LISpec of    *)
(* module LiveInternalMemory with the substitutions                        *)
(*                                                                         *)
(* (2)   mem <- omem, ctl <- octl, buf <- obuf                             *)
(*                                                                         *)
(* We now use TLC to check (1).  Because TLC Version 1 cannot handle       *)
(* instantiation, we do the instantiation "by hand".  So, below is a copy  *)
(* of the definitions from module LiveInternalMemory with the              *)
(* substitutions (2) made, and with the names of all defined operators     *)
(* prefixed with "LM_Inner_".  (Had we used the actual INSTANCE            *)
(* statements, those names would actually be prefixed by "LM!Inner(mem,    *)
(* ctl, buf)!", where mem, ctl, and buf would be parameters of the         *)
(* definitions.)  These definitions are all the same as in module          *)
(* MCWriteThroughCache in the folder CachingMemory, except with the        *)
(* additional definitions of LM_Inner_vars, LM_Inner_Liveness,             *)
(* LM_Inner_Liveness2, and LM_Inner_LISpec.  The definitions of            *)
(* LM_Inner_Liveness and LM_Inner_Liveness2 are tricky.                    *)
(***************************************************************************)

LM_Inner_IInit ≜ ∧ omem ∈ [Adr→Val]
                 ∧ octl = [p ∈ Proc ↦ "rdy"] 
                 ∧ obuf = [p ∈ Proc ↦ NoVal] 
                 ∧ memInt ∈ InitMemInt

LM_Inner_TypeInvariant ≜ 
  ∧ omem ∈ [Adr→Val]
  ∧ octl ∈ [Proc → {"rdy", "busy","done"}] 
  ∧ obuf ∈ [Proc → MReq ∪ Val ∪ {NoVal}]

LM_Inner_Req(p) ≜ ∧ octl[p] = "rdy" 
         ∧ ∃ req ∈  MReq : 
                ∧ Send(p, req, memInt, memInt') 
                ∧ obuf' = [obuf EXCEPT ![p] = req]
                ∧ octl' = [octl EXCEPT ![p] = "busy"]
          ∧ UNCHANGED omem 

LM_Inner_Do(p) ≜ 
  ∧ octl[p] = "busy" 
  ∧ omem' = IF obuf[p].op = "Wr"
              THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val] 
              ELSE omem 
  ∧ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                  THEN NoVal
                                  ELSE omem[obuf[p].adr]]
  ∧ octl' = [octl EXCEPT ![p] = "done"] 
  ∧ UNCHANGED memInt 

LM_Inner_Rsp(p) ≜ ∧ octl[p] = "done"
                  ∧ Reply(p, obuf[p], memInt, memInt')
                  ∧ octl' = [octl EXCEPT ![p]= "rdy"]
                  ∧ UNCHANGED ⟨omem, obuf⟩ 

LM_Inner_INext ≜ 
     ∃ p ∈ Proc: LM_Inner_Req(p) ∨ LM_Inner_Do(p) ∨ LM_Inner_Rsp(p) 

LM_Inner_ISpec ≜ 
    LM_Inner_IInit  ∧  □[LM_Inner_INext]_⟨memInt, omem, octl, obuf⟩

LM_Inner_vars ≜ ⟨memInt, omem, octl, obuf⟩


LM_Inner_EnabledDo(p)  ≜ octl[p] = "busy" 
  (*************************************************************************)
  (* The instantiation of ENABLED Do(p).  See the section titled           *)
  (* "Refinement Mappings and Fairness".                                   *)
  (*************************************************************************)
  
LM_Inner_EnabledRsp(p) ≜ octl[p] = "done"
  (*************************************************************************)
  (* The instantiation of ENABLED Rsp(p).  See the section titled          *)
  (* "Refinement Mappings and Fairness".                                   *)
  (*************************************************************************)


(***************************************************************************)
(* See the See the section titled "Refinement Mappings and Fairness".  for *)
(* an explanation of why the following are the appropriate definitions of  *)
(* LM_Inner_Liveness and LM_Inner_Liveness2.                               *)
(***************************************************************************)
LM_Inner_Liveness ≜ 
  ∀ p ∈ Proc : 
    ∧ □◇¬LM_Inner_EnabledDo(p) ∨ □◇⟨LM_Inner_Do(p)⟩_LM_Inner_vars
    ∧ □◇¬LM_Inner_EnabledRsp(p) ∨ □◇⟨LM_Inner_Rsp(p)⟩_LM_Inner_vars

LM_Inner_Liveness2 ≜ 
  ∀ p ∈ Proc : 
    ∨ □◇¬(LM_Inner_EnabledDo(p) ∨ LM_Inner_EnabledRsp(p))
    ∨ □◇⟨LM_Inner_Do(p) ∨ LM_Inner_Rsp(p)⟩_LM_Inner_vars

  
LM_Inner_LISpec ≜ LM_Inner_ISpec ∧ LM_Inner_Liveness2

LM_Inner_LivenessProperty ≜ 
   ∀ p ∈ Proc : (octl[p] = "req") ↝ (octl[p] = "rdy")

=============================================================================