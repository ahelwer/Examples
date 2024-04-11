------------------ MODULE AsynchInterface ---------------------
EXTENDS Naturals
CONSTANT  Data
VARIABLES val, rdy, ack

TypeInvariant ≜ ∧ val ∈ Data
                ∧ rdy ∈ {0, 1}
                ∧ ack ∈ {0, 1}
---------------------------------------------------------------
Init ≜ ∧ val ∈ Data
       ∧ rdy ∈ {0, 1}
       ∧ ack = rdy

Send ≜ ∧ rdy = ack
       ∧ val' ∈ Data
       ∧ rdy' = 1 - rdy
       ∧ UNCHANGED ack

Rcv  ≜ ∧ rdy ≠ ack
       ∧ ack' = 1 - ack
       ∧ UNCHANGED ⟨val, rdy⟩

Next ≜ Send ∨ Rcv

Spec ≜ Init ∧ □[Next]_⟨val, rdy, ack⟩
---------------------------------------------------------------
THEOREM Spec ⇒ □TypeInvariant
===============================================================