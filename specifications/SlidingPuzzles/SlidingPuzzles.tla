--------------------------- MODULE SlidingPuzzles ---------------------------
EXTENDS Integers

VARIABLE board

W ≜ 4 H ≜ 5
Pos ≜ (0 ‥ W - 1) × (0 ‥ H - 1)
Piece ≜ SUBSET Pos
                                          
Klotski ≜ {{⟨0, 0⟩, ⟨0, 1⟩},
            {⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩},
            {⟨3, 0⟩, ⟨3, 1⟩},{⟨0, 2⟩, ⟨0, 3⟩},
            {⟨1, 2⟩, ⟨2, 2⟩},{⟨3, 2⟩, ⟨3, 3⟩},
            {⟨1, 3⟩}, {⟨2, 3⟩}, {⟨0, 4⟩}, {⟨3, 4⟩}}
            
KlotskiGoal ≜ {⟨1, 3⟩, ⟨1, 4⟩, ⟨2, 3⟩, ⟨2, 4⟩} ∉ board
            
ChooseOne(S, P(_)) ≜ CHOOSE x ∈ S : P(x) ∧ ∀ y ∈ S : P(y) ⇒ y = x

TypeOK ≜ board ∈ SUBSET Piece

(***************************************************************************)
(* Given a position and a set of empty positions return a set of           *)
(* appropriately filtered von Neumann neighborhood points                  *)
(***************************************************************************)
dir(p, es) ≜ LET dir ≜ {⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, -1⟩}
              IN {d ∈ dir : ∧ ⟨p[1] + d[1], p[2] + d[2]⟩ ∈ Pos
                            ∧ ⟨p[1] + d[1], p[2] + d[2]⟩ ∉ es}

(***************************************************************************)
(* Given a position and a unit translation vector return a pair of         *)
(* pieces, before and after translation in opposite this vector direction  *)
(***************************************************************************)      
move(p, d) ≜ LET s ≜ ⟨p[1] + d[1], p[2] + d[2]⟩
                  pc ≜ ChooseOne(board, LAMBDA pc : s ∈ pc)
              IN ⟨pc, {⟨q[1] - d[1], q[2] - d[2]⟩ : q ∈ pc}⟩
           
(***************************************************************************)
(* Given specific free position and a set of all free positions return     *)
(* a set of boards updated by moving appropriate pieces to that            *)
(* free position                                                           *)
(***************************************************************************)                 
update(e, es) ≜ LET dirs  ≜ dir(e, es)
                     moved ≜ {move(e, d) : d ∈ dirs}
                     free  ≜ {⟨pc, m⟩ ∈ moved :
                                 ∧ m ∩ (UNION (board \ {pc})) = {}
                                 ∧ ∀ p ∈ m : p ∈ Pos}
                 IN {(board \ {pc}) ∪ {m} : ⟨pc, m⟩ ∈ free}

Init ≜ board = Klotski
        
Next ≜ LET empty ≜ Pos \ UNION board
        IN  ∃ e ∈ empty : board' ∈ update(e, empty)

=============================================================================
