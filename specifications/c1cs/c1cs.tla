-------------------------------- MODULE c1cs --------------------------------

(* An encoding of the consensus algorithm with crash faults in one communication 
   step [1]. Here we consider only the algorithm itself (Fig. 1), without looking  
   at the underlying consensus. 
   
   [1] Brasileiro, Francisco, et al. "Consensus in one communication step." 
   Parallel Computing Technologies (2001): 42-50.
                                                               
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 3 * T < N ∧ 0 ≤ F ∧ F ≤ T ∧ 0 < N

VARIABLES pc, v, dValue, bcastMsg, rcvdMsg

vars ≜ ⟨ pc, v, dValue, bcastMsg, rcvdMsg ⟩

Proc ≜ 1‥N      (* all processes, including the faulty ones *)

(* for program counters *)
Location ≜ { "PROPOSE", "DECIDE", "CALL", "CRASH", "DONE" }  

(* User-defined operators to create messages *)
makeProposedMsg(v_i, i) ≜ [ type ↦ "Proposed", value ↦ v_i, sndr ↦ i ]
makeDecisionMsg(v_i, i ) ≜ [ type ↦ "Decision", value ↦ v_i, sndr ↦ i ]

(* Set of messages *)
PMsg ≜ [ type : {"Proposed"} , value : Values, sndr : Proc ]
DMsg ≜ [ type : {"Decision"}, value : Values, sndr : Proc ]
Msg ≜ PMsg ∪ DMsg 

(* Initial step *)
Init ≜     
  ∧ v ∈ [ Proc → Values ]           (* Every process proposes randomly a value. *)
  ∧ pc = [ i ∈ Proc ↦ "PROPOSE" ]  (* Every process will vote for its value.   *)
  ∧ dValue = [ i ∈ Proc ↦ Bottom ] (* No process decides.                      *)    
  ∧ bcastMsg = {}                      (* No messages were sent.                   *)
  ∧ rcvdMsg = [ i ∈ Proc ↦ {} ]    (* No messages were received.               *)   
    
(* If there are less than F faulty process, process i crashes. *)    
Crash(i) ≜
  ∧ Cardinality( { p ∈ Proc : pc[p] ≠ "CRASH" } ) <  F
  ∧ pc[i] ≠ "CRASH"  
  ∧ pc' = [ pc EXCEPT ![i] = "CRASH" ]     
  ∧ UNCHANGED ⟨ dValue, v, bcastMsg, rcvdMsg ⟩
        
(* Receives a new message. *)        
Receive(i) ≜
  ∧ pc[i] ≠ "CRASH"
  ∧ ∃ sndr ∈ Proc, msg ∈ Msg:
        ∧ msg ∈ bcastMsg       
        ∧ msg ∉ rcvdMsg[i]
        ∧ rcvdMsg' = [ rcvdMsg EXCEPT ![i] = rcvdMsg[i] ∪ { msg } ]             
        ∧ UNCHANGED ⟨ pc, v, dValue, bcastMsg ⟩                           
   
(* Broadcasts PROPOSED(v_i) *)    
Propose(i) ≜    
  ∧ pc[i] = "PROPOSE"
  ∧ pc' = [ pc EXCEPT ![i] = "DECIDE" ]
  ∧ bcastMsg' = bcastMsg ∪ { makeProposedMsg(v[i], i) }
  ∧ UNCHANGED ⟨ v, dValue, rcvdMsg ⟩    
   
(* If a process received PHASE1(_, _) from at least N - F processes, 
 * it updates its local view and then estimates the expected value. 
 *)   
Core_T1(i) ≜ 
  ∧ pc[i] = "DECIDE"
  ∧ Cardinality({ msg ∈ rcvdMsg[i] : msg.type = "Proposed" }) ≥ N - T
  ∧ IF ∧ (∃ tV ∈ Values : ∀ msg ∈ rcvdMsg[i] : msg.type = "Proposed" ⇒ msg.value = tV) 
     THEN ∧ dValue' = [ dValue EXCEPT ![i] = CHOOSE tV ∈ Values : (Cardinality({ msg ∈ rcvdMsg[i] : msg.type = "Proposed" ∧ msg.value = tV }) ≥ N - T) ]
          ∧ bcastMsg' = bcastMsg ∪ { makeDecisionMsg(dValue'[i], i) } 
          ∧ pc' = [ pc EXCEPT ![i] = "DONE" ]
          ∧ UNCHANGED ⟨ v ⟩                 
     ELSE ∧ IF ∃ tV ∈ Values : Cardinality({ msg ∈ rcvdMsg[i] : msg.type = "Proposed" ∧ msg.value = tV }) ≥ N - 2 * T
             THEN ∧ v' = [ v EXCEPT ![i] = CHOOSE tV ∈ Values : (Cardinality({ msg ∈ rcvdMsg[i] : msg.type = "Proposed" ∧ msg.value = tV }) ≥ N - 2 * T) ]                    
                  ∧ UNCHANGED ⟨ dValue, bcastMsg ⟩
             ELSE UNCHANGED ⟨ dValue, v, bcastMsg ⟩
          ∧ pc' = [ pc EXCEPT ![i] = "CALL" ]   
  ∧ UNCHANGED ⟨ rcvdMsg ⟩                              

(* If process i received a DECISION message, it decides. *)     
T2(i) ≜
  ∧ pc[i] ≠ "DONE"
  ∧ pc[i] ≠ "CRASH"
  ∧ ∃ msg ∈ rcvdMsg[i]:
        ∧ msg.type = "Decision"
        ∧ dValue' = [ dValue EXCEPT ![i] = msg.value ]
        ∧ bcastMsg' = bcastMsg ∪ { makeDecisionMsg(dValue'[i], i) } 
        ∧ pc' = [ pc EXCEPT ![i] = "DONE" ]
        ∧ UNCHANGED ⟨ v, rcvdMsg ⟩
    
(* Just to avoid deadlock checking. *)    
DoNothing(i) ≜
  ∧ ∨ pc[i] = "CALL" 
    ∨ pc[i] = "DONE"
  ∧ UNCHANGED vars                    
            
Next ≜  
  ∃ i ∈ Proc: ∨ Crash(i)            
              ∨ Receive(i)      
              ∨ Propose(i)                                             
              ∨ Core_T1(i)
              ∨ T2(i)       
              ∨ DoNothing(i)     
                                    
Spec ≜ Init ∧ □[Next]_⟨ pc, v, dValue, bcastMsg, rcvdMsg ⟩
             ∧ WF_vars(∃ i ∈ Proc : ∨ Receive(i)            
                                    ∨ Propose(i)                                                
                                    ∨ Core_T1(i)
                                    ∨ T2(i))        

TypeOK ≜    
  ∧ v ∈ [ Proc → Values ] 
  ∧ pc ∈ [ Proc → Location ]       
  ∧ bcastMsg ∈ SUBSET (PMsg ∪ DMsg) 
  ∧ rcvdMsg ∈ [ Proc → SUBSET (PMsg ∪ DMsg) ]    
  ∧ dValue ∈ [ Proc → { Bottom } ∪ Values ]  
    
(* If a process decides v, then v was proposed by some process. *)
Validity ≜ ∀ i ∈ Proc : ((dValue[i] ≠ Bottom) ⇒ (∃ j ∈ Proc : dValue[i] = v[j]))

(* First line: No two processes decide differently. *)
(* Second line: If some process decided v, all process calling the underlying consensus algorithm propose v. *)
Agreement ≜ 
  ∧ ∀ i, j ∈ Proc : ((dValue[i] ≠ Bottom ∧ dValue[j] ≠ Bottom) ⇒ (dValue[i] = dValue[j]))
  ∧ ∀ i ∈ Proc : pc[i] = "CALL" ⇒ (∀ j ∈ Proc : pc[j] = "DONE" ⇒ v[i] = dValue[j]) 
    
(* Only talk about decided processes*)    
WeakAgreement ≜
  ∧ ∀ i, j ∈ Proc : ((dValue[i] ≠ Bottom ∧ dValue[j] ≠ Bottom) ⇒ (dValue[i] = dValue[j]))   

(* Every correct process eventually decides on some values. *)
Termination ≜ ◇(∀ i ∈ Proc : pc[i] = "CRASH" ∨ pc[i] = "DONE" ∨ pc[i] = "CALL")

(* Inductive strengthens usually are constraints on:
    - TypeOK,
    - PROPOSED messages and prefer values,            
    - values in messages which have sent,          
    - DECISION values and DECISION messages,    
    - the number of PROPOSED messages and DECISION messages,       
    - program counters and which messages have sent, 
    - DECISION values and processes' decisions,    
    - program counters and DECISION values,          
    - DECISION values and DECISION messages, 
    - DECISION values, and
    - which messages are sent and received.
   However, until now we don't what inductive strengthens are necessary to construct an
   inductive invariant with WeakAgreement. 
 *)
IndStrengthens ≜
  ∧ TypeOK
  (* Every correct process proposes only its prefer value. *)
  ∧ ∀ msg ∈ bcastMsg : (msg.type = "Proposed" ∧ (pc[msg.sndr] = "PROPOSE" ∨ pc[msg.sndr] = "DECIDE"))
                              ⇒ msg.value = v[msg.sndr]  
  (* A correct process can send at most one message for each kind of messages.  *)
  ∧ ∀ msg1 ∈ bcastMsg, msg2 ∈ bcastMsg : (msg1.sndr = msg2.sndr ∧ msg1.type = msg2.type) 
                                                    ⇒ msg1.value = msg2.value      
    
  (* All DECISION messages have the same value. *) 
  ∧ ∀ msg1 ∈ bcastMsg, msg2 ∈ bcastMsg : (msg1.type = "Decision" ∧ msg2.type = "Decision") 
                                                    ⇒ msg1.value = msg2.value    
  (* How to detect it automatically?
     Every DECISION message has the same value with at least N - T PROPOSED messages. *)  
  ∧ ∀ msg1 ∈ bcastMsg : msg1.type = "Decision" ⇒ (Cardinality( { msg2 ∈ bcastMsg : msg2.type = "Proposed" ∧ msg1.value = msg2.value} ) ≥ N - T)
  (* A process has not broadcasted any message before entering the location PROPOSE. *)
  ∧ ∀ i ∈ Proc : pc[i] = "PROPOSE" ⇒ ((∀ msg ∈ bcastMsg : msg.sndr ≠ i) )          
  (* How to detect it automatically?
     DECISION messages are always consistent with processes' decisions.  *)    
  ∧ ∀ i ∈ Proc : dValue[i] = Bottom ⇒ (∀ msg ∈ bcastMsg : msg.type = "Decision" ⇒ msg.sndr ≠ i)  
  (* A DECISION value must be different from Bottom *)       
  ∧ ∀ i ∈ Proc : pc[i] = "DONE" ⇒ dValue[i] ≠ Bottom     
  (* After deciding, every correct process needs to broadcast its decision immediately. *)          
  ∧ ∀ i ∈ Proc : dValue[i] ≠ Bottom ⇒ (∃ msg ∈ bcastMsg : msg.sndr = i ∧ msg.type = "Decision" ∧ msg.value = dValue[i])                                                                                                         
  (* A process decides only after entering the locations PROPOSE and DECIDE. *)  
  ∧ ∀ i ∈ Proc : dValue[i] ≠ Bottom ⇒ (pc[i] ≠ "PROPOSE" ∧ pc[i] ≠ "DECIDE")   
  (* A process has not decided before entering the locations PROPOSE and DECIDE. *)
  ∧ ∀ i ∈ Proc : (pc[i] = "PROPOSE" ∨ pc[i] = "DECIDE") ⇒ ((∀ msg ∈ bcastMsg : dValue[i] = Bottom) )
  (* Every received message were broadcasted by some process. *)
  ∧ ∀ i ∈ Proc: rcvdMsg[i] ⊆ bcastMsg   
  
  
=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:28:37 CEST 2018 by tthai
