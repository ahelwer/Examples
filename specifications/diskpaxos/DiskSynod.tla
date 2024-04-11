----------------------------- MODULE DiskSynod -----------------------------

EXTENDS Synod, FiniteSets

CONSTANTS Ballot(_), Disk, IsMajority(_)
ASSUME ∧ ∀ p ∈ Proc : ∧ Ballot(p) ⊆ {n ∈ ℕ : n > 0}
                      ∧ ∀ q ∈ Proc \ {p} : Ballot(p) ∩ Ballot(q) = {}
       ∧ IsMajority(Disk)
       ∧ ∀ S, T ∈ SUBSET Disk :
              IsMajority(S) ∧ IsMajority(T) ⇒ (S ∪ T ≠ {})

DiskBlock ≜ [mbal : (UNION {Ballot(p) : p ∈ Proc}) ∪ {0},
              bal  : (UNION {Ballot(p) : p ∈ Proc}) ∪ {0},
              inp  : Inputs ∪ {NotAnInput}]

InitDB ≜ [mbal ↦ 0, bal ↦ 0, inp ↦ NotAnInput]

VARIABLES disk , dblock , phase, disksWritten, blocksRead

vars ≜ ⟨input, output, disk , phase, dblock , disksWritten, blocksRead⟩

Init ≜ ∧ input ∈ [Proc → Inputs]
       ∧ output = [p ∈ Proc ↦ NotAnInput]
       ∧ disk = [d ∈ Disk ↦ [p ∈ Proc ↦ InitDB ]]
       ∧ phase = [p ∈ Proc ↦ 0]
       ∧ dblock = [p ∈ Proc ↦ InitDB ]
       ∧ disksWritten = [p ∈ Proc ↦ {}]
       ∧ blocksRead = [p ∈ Proc ↦ [d ∈ Disk ↦ {}]]
       
hasRead (p, d , q) ≜ ∃ br ∈ blocksRead [p][d ] : br .proc = q

allBlocksRead(p) ≜
  LET allRdBlks ≜ UNION {blocksRead [p][d ] : d ∈ Disk }
  IN {br.block : br ∈ allRdBlks}

InitializePhase(p) ≜
  ∧ disksWritten' = [disksWritten EXCEPT ![p] = {}]
  ∧ blocksRead' = [blocksRead EXCEPT ![p] = [d ∈ Disk ↦ {}]]

StartBallot(p) ≜
  ∧ phase[p] ∈ {1, 2}
  ∧ phase' = [phase EXCEPT ![p] = 1]
  ∧ ∃ b ∈ Ballot(p) : ∧ b > dblock [p].mbal
                      ∧ dblock' = [dblock EXCEPT ![p].mbal = b]
  ∧ InitializePhase(p)
  ∧ UNCHANGED ⟨input, output, disk⟩

Phase1or2Write(p, d) ≜
  ∧ phase[p] ∈ {1, 2}
  ∧ disk' = [disk EXCEPT ![d][p] = dblock[p]]
  ∧ disksWritten' = [disksWritten EXCEPT ![p] = @ ∪ {d}]
  ∧ UNCHANGED ⟨input, output, phase, dblock , blocksRead⟩

Phase1or2Read (p, d, q) ≜
  ∧ d ∈ disksWritten[p]
  ∧ IF disk [d ][q].mbal < dblock [p].mbal
     THEN ∧ blocksRead' = 
                [blocksRead EXCEPT
                    ![p][d ] = @ ∪ {[block ↦ disk [d ][q], proc ↦ q]}]
          ∧ UNCHANGED ⟨input, output, disk , phase, dblock , disksWritten⟩
     ELSE StartBallot(p)

EndPhase1or2(p) ≜
  ∧ IsMajority({d ∈ disksWritten[p] :
                    ∀ q ∈ Proc \ {p} : hasRead (p, d , q)})
  ∧ ∨ ∧ phase[p] = 1
      ∧ dblock' =
              [dblock EXCEPT
                ![p].bal = dblock [p].mbal,
                ![p].inp =
                    LET blocksSeen ≜ allBlocksRead(p) ∪ {dblock [p]}
                        nonInitBlks ≜
                            {bs ∈ blocksSeen : bs.inp ≠ NotAnInput}
                        maxBlk ≜
                            CHOOSE b ∈ nonInitBlks :
                                ∀ c ∈ nonInitBlks : b.bal ≥ c.bal
                    IN IF nonInitBlks = {} THEN input[p]
                       ELSE maxBlk .inp ]
      ∧ UNCHANGED output
    ∨ ∧ phase[p] = 2
      ∧ output' = [output EXCEPT ![p] = dblock [p].inp]
      ∧ UNCHANGED dblock
  ∧ phase' = [phase EXCEPT ![p] = @ + 1]
  ∧ InitializePhase(p)
  ∧ UNCHANGED ⟨input, disk⟩

Fail(p) ≜
  ∧ ∃ ip ∈ Inputs : input' = [input EXCEPT ![p] = ip]
  ∧ phase' = [phase EXCEPT ![p] = 0]
  ∧ dblock' = [dblock EXCEPT ![p] = InitDB]
  ∧ output' = [output EXCEPT ![p] = NotAnInput]
  ∧ InitializePhase(p)
  ∧ UNCHANGED disk

Phase0Read(p, d) ≜
  ∧ phase[p] = 0
  ∧ blocksRead' = [blocksRead EXCEPT
                        ![p][d ] = @ ∪ {[block ↦ disk [d][p], proc ↦ p]}]
  ∧ UNCHANGED ⟨input, output, disk , phase, dblock , disksWritten⟩
  

EndPhase0(p) ≜
  ∧ phase[p] = 0
  ∧ IsMajority({d ∈ Disk : hasRead (p, d, p)})
  ∧ ∃ b ∈ Ballot(p) :
        ∧ ∀ r ∈ allBlocksRead (p) : b > r.mbal
        ∧ dblock' = [dblock EXCEPT
                        ![p] = [(CHOOSE r ∈ allBlocksRead (p) :
                                     ∀ s ∈ allBlocksRead (p) : r .bal ≥ s.bal)
                                  EXCEPT !.mbal = b]]
  ∧ InitializePhase(p)
  ∧ phase' = [phase EXCEPT ![p] = 1]
  ∧ UNCHANGED ⟨input, output, disk⟩

Next ≜ ∃ p ∈ Proc :
          ∨ StartBallot(p)
          ∨ ∃ d ∈ Disk : ∨ Phase0Read (p, d)
                         ∨ Phase1or2Write(p, d)
                         ∨ ∃ q ∈ Proc \ {p} : Phase1or2Read (p, d, q)
          ∨ EndPhase1or2(p)
          ∨ Fail(p)
          ∨ EndPhase0(p)

DiskSynodSpec ≜ Init ∧ □[Next]_vars

THEOREM DiskSynodSpec ⇒ SynodSpec


=============================================================================
\* ModIFication History
\* Last modIFied Sat Jan 26 14:03:35 CET 2019 by tthai
\* Created Sat Jan 26 12:19:05 CET 2019 by tthai