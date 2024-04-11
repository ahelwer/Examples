--------------------------- MODULE ChannelRefinement ------------------------
EXTENDS Naturals, Sequences
VARIABLES h, l

ErrorVal ≜  CHOOSE v : v ∉ [val : 1‥12, rdy : {0, 1}, ack : {0, 1}]

BitSeqToNat[s ∈ Seq({0,1})] ≜
   IF  s = ⟨ ⟩  THEN  0  ELSE  Head(s) + 2 * BitSeqToNat[Tail(s)]

H ≜ INSTANCE Channel WITH chan ← h, Data ← 1‥12
L ≜ INSTANCE Channel WITH chan ← l, Data ← {0,1}
  ---------------------------- MODULE Inner ---------------------------------
  VARIABLE bitsSent

  Init ≜ ∧ bitsSent = ⟨ ⟩
         ∧ IF L!Init THEN H!Init
                       ELSE h = ErrorVal 

  SendBit ≜ ∃ b ∈ {0, 1}: 
                ∧ L!Send(b) 
                ∧ IF Len(bitsSent) < 3
                     THEN ∧ bitsSent' = ⟨b⟩ ∘ bitsSent
                          ∧ UNCHANGED h 
                     ELSE ∧ bitsSent'= ⟨⟩
                          ∧ H!Send(BitSeqToNat[⟨b⟩ ∘ bitsSent])

  RcvBit ≜ ∧ L!Rcv 
           ∧ IF bitsSent = ⟨ ⟩ THEN H!Rcv  
                                   ELSE UNCHANGED h 
           ∧ UNCHANGED bitsSent

  Error ≜ ∧ l' ≠ l
          ∧ ¬((∃ b ∈ {0,1} : L!Send(b)) ∨ L!Rcv) 
          ∧ h' = ErrorVal

  Next ≜ SendBit ∨ RcvBit ∨ Error 

  InnerIR ≜ Init ∧ □[Next]_⟨l,h,bitsSent⟩
  ===========================================================================
I(bitsSent) ≜ INSTANCE Inner 
IR ≜ \EE bitsSent : I(bitsSent)!InnerIR
=============================================================================