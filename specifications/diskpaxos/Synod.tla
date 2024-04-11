------------------------------- MODULE Synod -------------------------------

EXTENDS Naturals

CONSTANTS N , Inputs
ASSUME (N ∈ ℕ) ∧ (N > 0)

Proc ≜ 1‥N

NotAnInput ≜ CHOOSE c : c ∉ Inputs

VARIABLES input, output

------------------------------- MODULE Inner -------------------------------

VARIABLES allInput, chosen

IInit ≜ ∧ input ∈ [Proc → Inputs]
        ∧ output = [p ∈ Proc ↦ NotAnInput]
        ∧ chosen = NotAnInput
        ∧ allInput = {input[p] : p ∈ Proc}

IChoose(p) ≜
  ∧ output[p] = NotAnInput
  ∧ IF chosen = NotAnInput
     THEN ∃ ip ∈ allInput : ∧ chosen' = ip
                            ∧ output' = [output EXCEPT ![p] = ip]
     ELSE ∧ output' = [output EXCEPT ![p] = chosen]
          ∧ UNCHANGED chosen
  ∧ UNCHANGED ⟨input, allInput⟩

IFail(p) ≜
  ∧ output' = [output EXCEPT ![p] = NotAnInput]
  ∧ ∃ ip ∈ Inputs : ∧ input' = [input EXCEPT ![p] = ip]
                    ∧ allInput = allInput ∪ {ip}
  ∧ UNCHANGED chosen

INext ≜ ∃ p ∈ Proc : IChoose(p) ∨ IFail (p)

ISpec ≜ IInit ∧ □[INext]_⟨input, output, chosen, allInput⟩

=============================================================================

IS(chosen, allInput) ≜ INSTANCE Inner

SynodSpec ≜ \EE chosen, allInput : IS(chosen, allInput)!ISpec



=============================================================================
\* ModIFication History
\* Last modIFied Sat Jan 26 14:27:38 CET 2019 by tthai
\* Created Sat Jan 26 14:17:53 CET 2019 by tthai