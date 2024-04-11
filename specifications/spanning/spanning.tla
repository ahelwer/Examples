------------------------------ MODULE spanning ------------------------------
EXTENDS Integers
CONSTANTS Proc, NoPrnt, root, nbrs
ASSUME NoPrnt ∉ Proc ∧ nbrs ⊆ Proc × Proc
VARIABLES prnt, rpt, msg
vars ≜ ⟨prnt, rpt, msg⟩ 
             
Init ≜ ∧ prnt = [i ∈ Proc ↦ NoPrnt]
       ∧ rpt = [i ∈ Proc ↦ FALSE]
       ∧ msg = {}

CanSend(i, j) ≜  (⟨i, j⟩ ∈ nbrs) ∧ (i = root ∨ prnt[i] ≠ NoPrnt)

Update(i, j) ≜ ∧ prnt' = [prnt EXCEPT ![i] = j]
               ∧ UNCHANGED ⟨rpt, msg⟩
    
Send(i) ≜ ∃ k ∈ Proc: ∧ CanSend(i, k) ∧ (⟨i, k⟩ ∉ msg)
                      ∧ msg' = msg ∪ {⟨i, k⟩}
                      ∧ UNCHANGED ⟨prnt, rpt⟩
                                                                                    
Parent(i) ≜ ∧ prnt[i] ≠ NoPrnt ∧ ¬rpt[i]
            ∧ rpt' = [rpt EXCEPT ![i] = TRUE] 
            ∧ UNCHANGED ⟨msg, prnt⟩
             
Next ≜ ∃ i, j ∈ Proc: IF i ≠ root ∧ prnt[i] = NoPrnt ∧ ⟨j, i⟩ ∈ msg
                          THEN Update(i, j)
                          ELSE ∨ Send(i) ∨ Parent(i) 
                               ∨ UNCHANGED ⟨prnt, msg, rpt⟩                   
                                                        
Spec ≜ ∧ Init ∧ □[Next]_vars 
       ∧ WF_vars(∃ i, j ∈ Proc: IF i ≠ root ∧ prnt[i] = NoPrnt ∧ ⟨j, i⟩ ∈ msg
                                     THEN Update(i, j)
                                     ELSE ∨ Send(i) ∨ Parent(i) 
                                          ∨ UNCHANGED ⟨prnt, msg, rpt⟩)
                                           
TypeOK ≜ ∧ ∀ i ∈ Proc : prnt[i] = NoPrnt ∨ ⟨i, prnt[i]⟩ ∈ nbrs             
         ∧ rpt ∈ [Proc → BOOLEAN]  
         ∧ msg ⊆ Proc × Proc
  
Termination ≜ ◇(∀ i ∈ Proc : i = root ∨ (prnt[i] ≠ NoPrnt ∧ ⟨i, prnt[i]⟩ ∈ nbrs)) 

OneParent ≜ □[∀ i ∈ Proc : prnt[i] ≠ NoPrnt ⇒ prnt[i] = prnt'[i]]_vars

SntMsg ≜ ∀ i ∈ Proc: (i ≠ root ∧ prnt[i] = NoPrnt ⇒ ∀ j ∈ Proc: ⟨i ,j⟩ ∉ msg)

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:30:26 CEST 2018 by tthai