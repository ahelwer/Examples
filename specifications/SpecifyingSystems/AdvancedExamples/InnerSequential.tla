------------------------ MODULE InnerSequential -----------------------------
EXTENDS RegisterInterface, Naturals, Sequences, FiniteSets
VARIABLE opQ, mem
-----------------------------------------------------------------------------
Done    ≜ CHOOSE v : v ∉ Reg
-----------------------------------------------------------------------------
DataInvariant ≜ 
  ∧ RegFileTypeInvariant
  ∧ opQ ∈ [Proc → Seq([req : Request, reg : Reg ∪ {Done}])]
  ∧ mem ∈ [Adr → Val]
  ∧ ∀ p ∈ Proc : ∀ r ∈ Reg :
       Cardinality ({i ∈ DOMAIN opQ[p] : opQ[p][i].reg = r})
         = IF regFile[p][r].op = "Free" THEN 0 ELSE 1

Init ≜ ∧ regFile ∈ [Proc → [Reg → FreeRegValue]]
       ∧ opQ = [p ∈ Proc ↦ ⟨ ⟩]
       ∧ mem ∈ [Adr → Val]
-----------------------------------------------------------------------------
IssueRequest(proc, req, reg) ≜
  ∧ regFile[proc][reg].op = "Free"
  ∧ regFile' = [regFile EXCEPT ![proc][reg] = req]
  ∧ opQ' = [opQ EXCEPT ![proc] = Append(@, [req ↦ req, reg ↦ reg])]
  ∧ UNCHANGED mem

RespondToRd(proc, reg) ≜
  ∧ regFile[proc][reg].op = "Rd"
  ∧ ∃ val ∈ Val : 
       ∧ regFile' = [regFile EXCEPT ![proc][reg].val = val,
                                     ![proc][reg].op  = "Free"]
       ∧ opQ' = LET idx ≜ CHOOSE i ∈ DOMAIN opQ[proc] : 
                                         opQ[proc][i].reg = reg
                 IN [opQ EXCEPT ![proc][idx].req.val = val,
                                ![proc][idx].reg     = Done ]
  ∧ UNCHANGED mem

RespondToWr(proc, reg) ≜
  ∧ regFile[proc][reg].op = "Wr"
  ∧ regFile' = [regFile EXCEPT ![proc][reg].op  = "Free"]
  ∧ LET idx ≜ CHOOSE i ∈ DOMAIN opQ[proc] : opQ[proc][i].reg = reg
     IN  opQ' = [opQ EXCEPT ![proc][idx].reg = Done]
  ∧ UNCHANGED mem

RemoveOp(proc) ≜
  ∧ opQ[proc] ≠ ⟨ ⟩
  ∧ Head(opQ[proc]).reg = Done  
  ∧ mem' = IF Head(opQ[proc]).req.op = "Rd"
              THEN mem
              ELSE [mem EXCEPT ![Head(opQ[proc]).req.adr] = 
                                   Head(opQ[proc]).req.val]
  ∧ opQ' = [opQ EXCEPT ![proc] = Tail(@)]
  ∧ UNCHANGED regFile

Internal(proc)  ≜ 
    ∧ RemoveOp(proc)
    ∧ (Head(opQ[proc]).req.op = "Rd") ⇒
            (mem[Head(opQ[proc]).req.adr] = Head(opQ[proc]).req.val)

Next ≜ ∃ proc ∈ Proc:
           ∨ ∃ reg ∈ Reg :
                  ∨ ∃ req ∈ Request : IssueRequest(proc, req, reg)
                  ∨ RespondToRd(proc, reg)
                  ∨ RespondToWr(proc, reg)
           ∨ Internal(proc)
-----------------------------------------------------------------------------
Spec ≜
  ∧ Init 
  ∧ □[Next]_⟨regFile, opQ, mem⟩
  ∧ ∀ proc ∈ Proc, reg ∈ Reg :
        WF_⟨regFile, opQ, mem⟩(RespondToRd(proc, reg) 
                                        ∨ RespondToWr(proc, reg))
  ∧ ∀ proc ∈ Proc : WF_⟨regFile, opQ, mem⟩(RemoveOp(proc))

-----------------------------------------------------------------------------
THEOREM Spec ⇒ □DataInvariant
=============================================================================