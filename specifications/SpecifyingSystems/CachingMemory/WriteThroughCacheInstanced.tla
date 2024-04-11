-------------------- MODULE WriteThroughCacheInstanced ----------------------
(***************************************************************************)
(* This module is a version of module WriteThroughCache with the INSTANCE  *)
(* statements removed, because Version 1 of TLC cannot handle              *)
(* instantiation.  The one INSTANCE statement that we need to run TLC is   *)
(* replaced by the equivalent definitions.  Another INSTANCE statement,    *)
(* not needed for running TLC, is just commented out.                      *)
(***************************************************************************)

EXTENDS Naturals, Sequences, MemoryInterface 
VARIABLES wmem, ctl, buf, cache, memQ 
CONSTANT QLen
ASSUME (QLen ∈ ℕ) ∧ (QLen > 0) 

(***************************************************************************)
(* At this point, module WriteThroughCache contains the statement          *)
(*                                                                         *)
(*    M == INSTANCE InternalMemory WITH mem <- wmem                        *)
(*                                                                         *)
(* We perform the instantiations below "by hand".  The text below is the   *)
(* body of module InternalMemory (minus its EXTENDS and its declarations), *)
(* with wmem substituted everywhere for mem, and with the names of all     *)
(* symbols it defines prefixed by "M_".  (The actual INSTANCE statement    *)
(* prefixes the names with "M!", but we use "_" instead of "!" because     *)
(* TLA+ doesn't allow "!" to be used in a symbol name except when it is    *)
(* added by instantiation.)                                                *)
(***************************************************************************)
M_IInit ≜ ∧ wmem ∈ [Adr→Val]
          ∧ ctl = [p ∈ Proc ↦ "rdy"] 
          ∧ buf = [p ∈ Proc ↦ NoVal] 
          ∧ memInt ∈ InitMemInt

M_TypeInvariant ≜ 
  ∧ wmem ∈ [Adr→Val]
  ∧ ctl ∈ [Proc → {"rdy", "busy","done"}] 
  ∧ buf ∈ [Proc → MReq ∪ Val ∪ {NoVal}]

M_Req(p) ≜ ∧ ctl[p] = "rdy" 
           ∧ ∃ req ∈  MReq : 
                  ∧ Send(p, req, memInt, memInt') 
                  ∧ buf' = [buf EXCEPT ![p] = req]
                  ∧ ctl' = [ctl EXCEPT ![p] = "busy"]
           ∧ UNCHANGED wmem 

M_Do(p) ≜ 
  ∧ ctl[p] = "busy" 
  ∧ wmem' = IF buf[p].op = "Wr"
              THEN [wmem EXCEPT ![buf[p].adr] = buf[p].val] 
              ELSE wmem 
  ∧ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                  THEN NoVal
                                  ELSE wmem[buf[p].adr]]
  ∧ ctl' = [ctl EXCEPT ![p] = "done"] 
  ∧ UNCHANGED memInt 

M_Rsp(p) ≜ ∧ ctl[p] = "done"
           ∧ Reply(p, buf[p], memInt, memInt')
           ∧ ctl' = [ctl EXCEPT ![p]= "rdy"]
           ∧ UNCHANGED ⟨wmem, buf⟩ 

M_INext ≜ ∃ p ∈ Proc: M_Req(p) ∨ M_Do(p) ∨ M_Rsp(p) 

M_ISpec ≜ M_IInit  ∧  □[M_INext]_⟨memInt, wmem, ctl, buf⟩
--------------------------------------------------------------
(***************************************************************************)
(* Below is the rest of module WriteThroughCache, except with each "!"     *)
(* replaced by "_".                                                        *)
(***************************************************************************)

Init ≜ ∧ M_IInit 
       ∧ cache = [p ∈ Proc ↦ [a ∈ Adr ↦ NoVal] ]
       ∧ memQ = ⟨ ⟩  
 
TypeInvariant ≜ 
  ∧ wmem  ∈ [Adr → Val]
  ∧ ctl   ∈ [Proc → {"rdy", "busy", "waiting", "done"}] 
  ∧ buf   ∈ [Proc → MReq ∪ Val ∪ {NoVal}]
  ∧ cache ∈ [Proc → [Adr → Val ∪ {NoVal}]] 
  ∧ memQ  ∈ Seq(Proc × MReq) 

Coherence ≜ ∀ p, q ∈ Proc, a ∈ Adr : 
                (NoVal ∉ {cache[p][a], cache[q][a]})
                      ⇒ (cache[p][a]=cache[q][a]) 
-----------------------------------------------------------------------------
Req(p) ≜ M_Req(p) ∧ UNCHANGED ⟨cache, memQ⟩ 
Rsp(p) ≜ M_Rsp(p) ∧ UNCHANGED ⟨cache, memQ⟩ 

RdMiss(p) ≜  ∧ (ctl[p] = "busy") ∧ (buf[p].op = "Rd") 
             ∧ cache[p][buf[p].adr] = NoVal 
             ∧ Len(memQ) < QLen
             ∧ memQ' = Append(memQ, ⟨p, buf[p]⟩)
             ∧ ctl' = [ctl EXCEPT ![p] = "waiting"]
             ∧ UNCHANGED ⟨memInt, wmem, buf, cache⟩

DoRd(p) ≜ 
  ∧ ctl[p] ∈ {"busy","waiting"} 
  ∧ buf[p].op = "Rd" 
  ∧ cache[p][buf[p].adr] ≠ NoVal
  ∧ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  ∧ ctl' = [ctl EXCEPT ![p] = "done"]
  ∧ UNCHANGED ⟨memInt, wmem, cache, memQ⟩ 

DoWr(p) ≜ 
  LET r ≜ buf[p]
  IN  ∧ (ctl[p] = "busy") ∧ (r.op = "Wr") 
      ∧ Len(memQ) < QLen
      ∧ cache' = [q ∈ Proc ↦ 
                    IF (p=q)  ∨  (cache[q][r.adr]≠NoVal)
                      THEN [cache[q] EXCEPT ![r.adr] = r.val]
                      ELSE cache[q] ]
      ∧ memQ' = Append(memQ, ⟨p, r⟩)
      ∧ buf' = [buf EXCEPT ![p] = NoVal]
      ∧ ctl' = [ctl EXCEPT ![p] = "done"]
      ∧ UNCHANGED ⟨memInt, wmem⟩ 

vmem  ≜  
  LET f[i ∈ 0 ‥ Len(memQ)] ≜ 
        IF i=0 THEN wmem
               ELSE IF memQ[i][2].op = "Rd"
                      THEN f[i-1]
                      ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] =
                                              memQ[i][2].val]
  IN f[Len(memQ)] 

MemQWr ≜ LET r ≜ Head(memQ)[2] 
          IN  ∧ (memQ ≠ ⟨ ⟩)  ∧   (r.op = "Wr") 
              ∧ wmem' = [wmem EXCEPT ![r.adr] = r.val] 
              ∧ memQ' = Tail(memQ) 
              ∧ UNCHANGED ⟨memInt, buf, ctl, cache⟩ 

MemQRd ≜ 
  LET p ≜ Head(memQ)[1] 
      r ≜ Head(memQ)[2] 
  IN  ∧ (memQ ≠ ⟨ ⟩ ) ∧ (r.op = "Rd")
      ∧ memQ' = Tail(memQ)
      ∧ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      ∧ UNCHANGED ⟨memInt, wmem, buf, ctl⟩  

Evict(p,a) ≜ ∧ (ctl[p] = "waiting") ⇒ (buf[p].adr ≠ a) 
             ∧ cache' = [cache EXCEPT ![p][a] = NoVal]
             ∧ UNCHANGED ⟨memInt, wmem, buf, ctl, memQ⟩ 

Next ≜ ∨ ∃ p∈ Proc : ∨ Req(p) ∨ Rsp(p) 
                     ∨ RdMiss(p) ∨ DoRd(p) ∨ DoWr(p) 
                     ∨ ∃ a ∈ Adr : Evict(p, a)
       ∨ MemQWr ∨ MemQRd    

Spec ≜ 
  Init ∧ □[Next]_⟨memInt, wmem, buf, ctl, cache, memQ⟩
-----------------------------------------------------------------------------
THEOREM Spec ⇒ □(TypeInvariant ∧ Coherence)
-----------------------------------------------------------------------------

(***************************************************************************)
(* We comment out the following instantiation and theorem, since TLC can't *)
(* do anything with them anyway.                                           *)
(***************************************************************************)
\* LM == INSTANCE Memory 
\* THEOREM Spec => LM_Spec 
==============================================================

THEOREM ISpec => []TypeInvariant
==============================================================