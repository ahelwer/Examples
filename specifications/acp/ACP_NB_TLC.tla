------------------------------ MODULE ACP_NB_TLC -------------------------------

\* ACP_SB, TLC ready

EXTENDS ACP_NB, TLC

Perms ≜ Permutations(participants) \* to benefit from symmetries

--------------------------------------------------------------------------------

\* AC4 rewritten in a way that is better handled by TLC

AC4_alt ≜ □[ ∧ (∀ i ∈ participants : participant[i].decision = commit 
                                ⇒ (participant'[i].decision = commit))
             ∧ (∀ j ∈ participants : participant[j].decision = abort  
                                ⇒ (participant'[j].decision = abort))]_⟨participant⟩

================================================================================