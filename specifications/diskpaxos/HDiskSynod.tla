----------------------------- MODULE HDiskSynod -----------------------------

EXTENDS DiskSynod
VARIABLES allInput, chosen

HInit ≜ ∧ Init
        ∧ chosen = NotAnInput
        ∧ allInput = {input[p] : p ∈ Proc}
        
HNext ≜ ∧ Next
        ∧ chosen' = LET hasOutput(p) ≜ output'[p] ≠ NotAnInput
                      IN IF ∨ chosen ≠ NotAnInput
                            ∨ ∀ p ∈ Proc : ¬hasOutput(p)
                         THEN chosen
                         ELSE output'[CHOOSE p ∈ Proc : hasOutput(p)]
        ∧ allInput' = allInput ∪ {input'[p] : p ∈ Proc}        
        

HInv1 ≜
  ∧ input ∈ [Proc → Inputs]
  ∧ output ∈ [Proc → Inputs ∪ {NotAnInput}]
  ∧ disk ∈ [Disk → [Proc → DiskBlock ]]
  ∧ phase ∈ [Proc → 0‥3]
  ∧ dblock ∈ [Proc → DiskBlock ]
  ∧ output ∈ [Proc → Inputs ∪ {NotAnInput}]
  ∧ disksWritten ∈ [Proc → SUBSET Disk ]
  ∧ blocksRead ∈ [Proc → [Disk → SUBSET [block : DiskBlock , proc : Proc]]]
  ∧ allInput ∈ SUBSET Inputs
  ∧ chosen ∈ Inputs ∪ {NotAnInput}
  
MajoritySet ≜ {D ∈ SUBSET Disk : IsMajority(D)}

blocksOf(p) ≜
  LET rdBy(q, d) ≜ {br ∈ blocksRead[q][d] : br.proc = p}
  IN {dblock[p]} ∪ {disk[d][p] : d ∈ Disk }
        ∪ {br.block : br ∈ UNION{rdBy(q, d) : q ∈ Proc, d ∈ Disk}}

allBlocks ≜ UNION {blocksOf(p) : p ∈ Proc}  

HInv2 ≜
  ∧ ∀ p ∈ Proc :
      ∀ bk ∈ blocksOf (p) : ∧ bk.mbal ∈ Ballot(p) ∪ {0}
                            ∧ bk.bal ∈ Ballot(p) ∪ {0}
                               (*/\ (bk.bal = 0) ≡ (bk.inp = NotAnInput)*)
                            ∧ (bk.bal = 0) ⇔ (bk.inp = NotAnInput)
                            ∧ bk.mbal ≥ bk.bal
                            ∧ bk.inp ∈ allInput ∪ {NotAnInput}
  ∧ ∀ p ∈ Proc, d ∈ Disk :
        ∧ (d ∈ disksWritten[p]) ⇒ ∧ phase[p] ∈ {1, 2}
                                  ∧ disk[d][p] = dblock[p]
        ∧ (phase[p] ∈ {1, 2}) ⇒ ∧ (blocksRead [p][d ] ≠ {}) ⇒
                                            (d ∈ disksWritten[p])
                                ∧ ¬hasRead (p, d, p)
  ∧ ∀ p ∈ Proc :
        ∧ (phase[p] = 0) ⇒ ∧ dblock[p] = InitDB
                           ∧ disksWritten[p] = {}
                           ∧ ∀ d ∈ Disk : ∀ br ∈ blocksRead[p][d] :
                                      ∧ br.proc = p
                                      ∧ br.block = disk [d ][p]
        ∧ (phase[p] ≠ 0) ⇒ ∧ dblock[p].mbal ∈ Ballot(p)
                           ∧ dblock[p].bal ∈ Ballot(p) ∪ {0}
                           ∧ ∀ d ∈ Disk : ∀ br ∈ blocksRead [p][d ] :
                                          br.block.mbal < dblock[p].mbal
        ∧ (phase[p] ∈ {2, 3}) ⇒ (dblock[p].bal = dblock[p].mbal)
        ∧ output[p] = IF phase[p] = 3 THEN dblock[p].inp ELSE NotAnInput
  ∧ chosen ∈ allInput ∪ {NotAnInput}
  ∧ ∀ p ∈ Proc : ∧ input[p] ∈ allInput
                 ∧ (chosen = NotAnInput) ⇒ (output[p] = NotAnInput)

HInv3 ≜ ∀ p, q ∈ Proc, d ∈ Disk :
              ∧ phase[p] ∈ {1, 2}
              ∧ phase[q] ∈ {1, 2}
              ∧ hasRead (p, d, q)
              ∧ hasRead (q, d, p)
            ⇒ ∨ [block ↦ dblock [q], proc ↦ q] ∈ blocksRead[p][d]
              ∨ [block ↦ dblock [p], proc ↦ p] ∈ blocksRead[q][d]

HInv4 ≜
  ∀ p ∈ Proc :
      ∧ (phase[p] ≠ 0) ⇒
            ∧ ∀ bk ∈ blocksOf(p) : dblock[p].mbal ≥ bk.bal
            ∧ ∀ D ∈ MajoritySet :
                    ∃ d ∈ D : ∧ dblock[p].mbal ≥ disk[d][p].mbal
                              ∧ dblock[p].bal ≥ disk[d][p].bal
      ∧ (phase[p] = 1) ⇒ (∀ bk ∈ blocksOf(p) : dblock[p].mbal > bk.bal)
      ∧ (phase[p] ∈ {2, 3}) ⇒
            (∃ D ∈ MajoritySet : ∀ d ∈ D : disk[d][p].mbal = dblock[p].bal)
      ∧ ∀ bk ∈ blocksOf(p) :
            ∃ D ∈ MajoritySet : ∀ d ∈ D : disk[d][p].mbal ≥ bk.bal

maxBalInp(b, v ) ≜ ∀ bk ∈ allBlocks : (bk.bal ≥ b) ⇒ (bk.inp = v)

HInv5 ≜
  ∀ p ∈ Proc :
    (phase[p] = 2) ⇒ ∨ maxBalInp(dblock[p].bal , dblock[p].inp)
                     ∨  ∃ D ∈ MajoritySet, q ∈ Proc :
                              ∀ d ∈ D : ∧ disk[d][q].mbal > dblock [p].bal
                                        ∧ ¬hasRead (p, d , q)

valueChosen(v) ≜
  ∃ b ∈ UNION {Ballot(p) : p ∈ Proc} :
      ∧ maxBalInp(b, v)
      ∧ ∃ p ∈ Proc, D ∈ MajoritySet :
              ∀ d ∈ D : ∧ disk[d][p].bal ≥ b
                        ∧ ∀ q ∈ Proc :
                                  ∧ phase[q] = 1
                                  ∧ dblock[q].mbal ≥ b
                                  ∧ hasRead(q, d, p)
                                ⇒ (∃ br ∈ blocksRead[q][d] : br.block.bal ≥ b)

HInv6 ≜ ∧ (chosen ≠ NotAnInput) ⇒ valueChosen(chosen)
        ∧ ∀ p ∈ Proc : output[p] ∈ {chosen, NotAnInput}



=============================================================================
\* Modification History
\* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
\* Created Sat Jan 26 15:23:57 CET 2019 by tthai