-------------------------- MODULE InnerSerial -------------------------------
EXTENDS RegisterInterface, Naturals, Sequences, FiniteSets, TLC
CONSTANT InitMem
VARIABLE opQ, opOrder
-----------------------------------------------------------------------------
opId      ≜ UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p ∈ Proc }
opIdQ(oi) ≜ opQ[oi.proc][oi.idx]

InitWr  ≜ CHOOSE v : v ∉ [proc : Proc, idx : ℕ]

Done ≜ CHOOSE v : v ∉ Reg

opVal ≜      [req : Request,   reg : Reg]         
         ∪ [req : WrRequest, reg : {Done}]  
         ∪ [req : RdRequest, reg : {Done}, source : opId ∪ {InitWr}]

goodSource(oi) ≜ 
  {InitWr} ∪ {o ∈ opId : ∧ opIdQ(o).req.op  = "Wr"
                         ∧ opIdQ(o).req.adr = opIdQ(oi).req.adr}
-----------------------------------------------------------------------------
DataInvariant ≜ 
  ∧ RegFileTypeInvariant

  ∧ opQ ∈ [Proc → Seq(opVal)]

  ∧ opOrder ⊆ (opId × opId)

  ∧ ∀ oi ∈ opId :
       ∧ ("source" ∈ DOMAIN opIdQ(oi)) ⇒ 
             ∧ opIdQ(oi).source ∈ goodSource(oi)
             ∧ opIdQ(oi).req.val = 
                   IF opIdQ(oi).source = InitWr
                     THEN InitMem[opIdQ(oi).req.adr]
                     ELSE opIdQ(opIdQ(oi).source).req.val
       ∧ (opIdQ(oi).reg ≠ Done) ⇒ 
             (opIdQ(oi).req = regFile[oi.proc][opIdQ(oi).reg])

  ∧ ∀ p ∈ Proc : ∀ r ∈ Reg :
       Cardinality ({i ∈ DOMAIN opQ[p] : opQ[p][i].reg = r})
         = IF regFile[p][r].op = "Free" THEN 0 ELSE 1

Init ≜ ∧ regFile ∈ [Proc → [Reg → FreeRegValue]]
       ∧ opQ = [p ∈ Proc ↦ ⟨ ⟩]
       ∧ opOrder = {}

totalOpOrder  ≜
  {R ∈ SUBSET (opId × opId) :
     ∧ ∀ oi, oj ∈ opId : 
             (oi = oj) ∨ (⟨oi, oj⟩ ∈ R)  ∨ (⟨oj, oi⟩ ∈ R)
     ∧ ∀ oi, oj, ok ∈ opId : 
           (⟨oi, oj⟩ ∈ R)  ∧ (⟨oj, ok⟩ ∈ R) ⇒ (⟨oi, ok⟩ ∈ R)
     ∧ ∀ oi ∈ opId : ⟨oi, oi⟩ ∉ R }

Serializable ≜
  ∃ R ∈ totalOpOrder :
     ∧ opOrder ⊆ R
     ∧ ∀ oi, oj ∈ opId :
          (oi.proc = oj.proc) ∧ (oi.idx < oj.idx) ⇒ (⟨oi, oj⟩ ∈ R)
     ∧ ∀ oi ∈ opId : 
           ("source" ∈ DOMAIN opIdQ(oi)) ⇒
               ¬ ( ∃ oj ∈ goodSource(oi) : 
                      ∧ ⟨oj, oi⟩ ∈ R
                      ∧ (opIdQ(oi).source ≠ InitWr) ⇒ 
                            (⟨opIdQ(oi).source, oj⟩ ∈ R) )
-----------------------------------------------------------------------------
UpdateOpOrder ≜ 
  ∧ opOrder' ∈ SUBSET(opId' × opId')
  ∧ opOrder ⊆ opOrder'
  ∧ Serializable'

IssueRequest(proc, req, reg) ≜
  ∧ regFile[proc][reg].op = "Free"
  ∧ regFile' = [regFile EXCEPT ![proc][reg] = req]
  ∧ opQ' = [opQ EXCEPT ![proc] = Append(@, [req ↦ req, reg ↦ reg])]
  ∧ UpdateOpOrder

RespondToWr(proc, reg) ≜
  ∧ regFile[proc][reg].op = "Wr"
  ∧ regFile' = [regFile EXCEPT ![proc][reg].op  = "Free"]
  ∧ LET idx ≜ CHOOSE i ∈ DOMAIN opQ[proc] : opQ[proc][i].reg = reg
     IN  opQ' = [opQ EXCEPT ![proc][idx].reg = Done]
  ∧ UpdateOpOrder

RespondToRd(proc, reg) ≜
  LET req ≜ regFile[proc][reg]
      idx ≜ CHOOSE i ∈ DOMAIN opQ[proc] : opQ[proc][i].reg = reg
  IN  ∧ req.op = "Rd"
      ∧ ∃ src ∈ goodSource([proc ↦ proc, idx ↦ idx]) :
           LET val ≜ IF src = InitWr THEN InitMem[req.adr]
                                      ELSE opIdQ(src).req.val
           IN  ∧ regFile' = [regFile EXCEPT ![proc][reg].val = val,
                                             ![proc][reg].op  = "Free"]
               ∧ opQ' = [opQ EXCEPT ![proc][idx] = 
                            [req    ↦ [req EXCEPT !.val = val],
                             reg    ↦ Done,
                             source ↦ src  ]]
      ∧ UpdateOpOrder

Internal ≜
   ∧ UNCHANGED ⟨regFile, opQ⟩
   ∧ UpdateOpOrder

Next ≜ ∨ ∃ proc ∈ Proc, reg ∈ Reg :
             ∨ ∃ req ∈ Request : IssueRequest(proc, req, reg)
             ∨ RespondToRd(proc, reg)
             ∨ RespondToWr(proc, reg)
       ∨ Internal
-----------------------------------------------------------------------------
Spec ≜
  ∧ Init 
  ∧ □[Next]_⟨regFile, opQ, opOrder⟩
  ∧ ∀ proc ∈ Proc, reg ∈ Reg :
      WF_⟨regFile, opQ, opOrder⟩(RespondToWr(proc, reg) 
                                        ∨ RespondToRd(proc, reg) )
  ∧ ∀ oi, oj ∈ [proc : Proc, idx : ℕ] : 
       (oi ≠ oj) ⇒ 
             WF_⟨regFile, opQ, opOrder⟩(
                   ∧ (oi ∈ opId) ∧ (oj ∈ opId)
                   ∧ Internal
                   ∧ (⟨oi, oj⟩ ∈ opOrder') ∨ (⟨oj, oi⟩ ∈ opOrder'))

=============================================================================