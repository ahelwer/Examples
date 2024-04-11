--------------------------- MODULE AlternatingBit ---------------------------
EXTENDS Naturals, Sequences
CONSTANTS Data
VARIABLES msgQ, 
          ackQ, 
          sBit, 
          sAck, 
          rBit, 
          sent, 
          rcvd  
-----------------------------------------------------------------------------
ABInit ≜ ∧ msgQ = ⟨ ⟩
         ∧ ackQ = ⟨ ⟩
         ∧ sBit ∈ {0, 1}
         ∧ sAck = sBit
         ∧ rBit = sBit
         ∧ sent ∈ Data
         ∧ rcvd ∈ Data

ABTypeInv ≜ ∧ msgQ ∈ Seq({0,1} × Data)
            ∧ ackQ ∈ Seq({0,1})
            ∧ sBit ∈ {0, 1}
            ∧ sAck ∈ {0, 1}
            ∧ rBit ∈ {0, 1}
            ∧ sent ∈ Data
            ∧ rcvd ∈ Data
-----------------------------------------------------------------------------
SndNewValue(d) ≜ 
  ∧ sAck = sBit
  ∧ sent' = d
  ∧ sBit' = 1 - sBit
  ∧ msgQ' = Append(msgQ, ⟨sBit', d⟩) 
  ∧ UNCHANGED ⟨ackQ, sAck, rBit, rcvd⟩

ReSndMsg ≜ 
  ∧ sAck ≠ sBit
  ∧ msgQ' = Append(msgQ, ⟨sBit, sent⟩)
  ∧ UNCHANGED ⟨ackQ, sBit, sAck, rBit, sent, rcvd⟩

RcvMsg ≜ 
  ∧ msgQ ≠ ⟨⟩
  ∧ msgQ' = Tail(msgQ)
  ∧ rBit' = Head(msgQ)[1] 
  ∧ rcvd' = Head(msgQ)[2] 
  ∧ UNCHANGED ⟨ackQ, sBit, sAck, sent⟩

SndAck ≜ ∧ ackQ' = Append(ackQ, rBit)
         ∧ UNCHANGED ⟨msgQ, sBit, sAck, rBit, sent, rcvd⟩

RcvAck ≜ ∧ ackQ ≠ ⟨ ⟩
         ∧ ackQ' = Tail(ackQ)
         ∧ sAck' = Head(ackQ)
         ∧ UNCHANGED ⟨msgQ, sBit, rBit, sent, rcvd⟩

Lose(q) ≜ 
   ∧ q ≠ ⟨ ⟩
   ∧ ∃ i ∈ 1‥Len(q) : 
          q' = [j ∈ 1‥(Len(q)-1) ↦ IF j < i THEN q[j] 
                                                 ELSE q[j+1] ]
   ∧ UNCHANGED ⟨sBit, sAck, rBit, sent, rcvd⟩

LoseMsg ≜ Lose(msgQ) ∧ UNCHANGED ackQ

LoseAck ≜ Lose(ackQ) ∧ UNCHANGED msgQ

ABNext ≜ ∨  ∃ d ∈ Data : SndNewValue(d) 
         ∨  ReSndMsg ∨ RcvMsg ∨ SndAck ∨ RcvAck 
         ∨  LoseMsg ∨ LoseAck 
-----------------------------------------------------------------------------
abvars ≜ ⟨ msgQ, ackQ, sBit, sAck, rBit, sent, rcvd⟩

ABFairness ≜ ∧ WF_abvars(ReSndMsg) ∧ WF_abvars(SndAck)   
             ∧ SF_abvars(RcvMsg) ∧ SF_abvars(RcvAck) 
-----------------------------------------------------------------------------
ABSpec ≜ ABInit ∧ □[ABNext]_abvars ∧ ABFairness
-----------------------------------------------------------------------------
THEOREM ABSpec ⇒ □ABTypeInv
=============================================================================