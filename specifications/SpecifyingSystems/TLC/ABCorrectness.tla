------------------- MODULE ABCorrectness --------------------
EXTENDS Naturals
CONSTANTS Data
VARIABLES sBit, sAck, rBit, sent, rcvd  
-------------------------------------------------------------
ABCInit ≜ ∧ sBit ∈ {0, 1}
          ∧ sAck = sBit
          ∧ rBit = sBit
          ∧ sent ∈ Data
          ∧ rcvd ∈ Data

CSndNewValue(d) ≜ ∧ sAck = sBit
                  ∧ sent' = d
                  ∧ sBit' = 1 - sBit
                  ∧ UNCHANGED ⟨sAck, rBit, rcvd⟩

CRcvMsg ≜ ∧ rBit ≠ sBit 
          ∧ rBit' = sBit
          ∧ rcvd' = sent
          ∧ UNCHANGED ⟨sBit, sAck, sent⟩

CRcvAck ≜ ∧ rBit ≠ sAck
          ∧ sAck' = rBit
          ∧ UNCHANGED ⟨sBit, rBit, sent, rcvd⟩

ABCNext ≜ ∨  ∃ d ∈ Data : CSndNewValue(d) 
          ∨  CRcvMsg ∨ CRcvAck 
-------------------------------------------------------------
cvars ≜ ⟨sBit, sAck, rBit, sent, rcvd⟩

TypeInv ≜ ∧ sBit ∈ {0, 1}
          ∧ sAck ∈ {0, 1}
          ∧ rBit ∈ {0, 1}
          ∧ sent ∈ Data
          ∧ rcvd ∈ Data

ABCFairness ≜ WF_cvars(CRcvMsg) ∧ WF_cvars(CRcvAck)   

ABCSpec ≜ ABCInit ∧ □[ABCNext]_cvars ∧ ABCFairness
==============================================================