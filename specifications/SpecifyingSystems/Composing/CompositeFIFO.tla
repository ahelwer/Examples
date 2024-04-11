--------------------------- MODULE CompositeFIFO ---------------------------- 
EXTENDS Naturals, Sequences
CONSTANT Message
VARIABLES in, out
-----------------------------------------------------------------------------
InChan  ≜ INSTANCE Channel WITH Data ← Message, chan ← in
OutChan ≜ INSTANCE Channel WITH Data ← Message, chan ← out
-----------------------------------------------------------------------------
SenderInit ≜ (in.rdy ∈ BOOLEAN) ∧ (in.val ∈ Message)
Sender ≜ 
  SenderInit ∧ □[∃ msg ∈ Message : InChan!Send(msg)]_⟨in.val, in.rdy⟩
-----------------------------------------------------------------------------
  ---------------------------- MODULE InnerBuf ------------------------------ 
  VARIABLE q
  BufferInit ≜ ∧ in.ack ∈ BOOLEAN
               ∧ q = ⟨ ⟩
               ∧ (out.rdy ∈ BOOLEAN) ∧ (out.val ∈ Message)

  BufRcv ≜ ∧ InChan!Rcv
           ∧ q' = Append(q, in.val) 
           ∧ UNCHANGED ⟨out.val, out.rdy⟩

  BufSend ≜ ∧ q ≠ ⟨ ⟩
            ∧ OutChan!Send(Head(q))
            ∧ q' = Tail(q)
            ∧ UNCHANGED in.ack

  InnerBuffer ≜ 
    BufferInit ∧ □[BufRcv ∨ BufSend]_⟨in.ack, q, out.val, out.rdy⟩
  ===========================================================================
Buf(q) ≜ INSTANCE InnerBuf
Buffer ≜ \EE q : Buf(q)!InnerBuffer
-----------------------------------------------------------------------------
ReceiverInit ≜ out.ack ∈ BOOLEAN
Receiver ≜ ReceiverInit ∧ □[OutChan!Rcv]_⟨in.val, in.rdy⟩
-----------------------------------------------------------------------------
IsChannel(c) ≜ c = [ack ↦ c.ack, val ↦ c.val, rdy ↦ c.rdy]
Spec ≜ ∧ □(IsChannel(in) ∧ IsChannel(out))
       ∧ (in.ack = in.rdy) ∧ (out.ack = out.rdy) 
       ∧ Sender ∧ Buffer ∧ Receiver
=============================================================================