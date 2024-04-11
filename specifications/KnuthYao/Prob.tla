------------------------------------------- MODULE Prob -------------------------------------------
EXTENDS Integers

VARIABLES p, state
vars ≜ ⟨p, state⟩

One ≜ 100000

a / b     ≜ IF b ≠ 0 THEN ⟨a, b⟩ ELSE CHOOSE x ∈ {} : TRUE
a ⊙ b ≜ (a[1]*b[1]) / (a[2]*b[2])
Norm(x)   ≜ x[1] ÷ x[2]

MarkovInit(Initial) ≜ 
        ∧ state = Initial
        ∧ p     = One/1

MarkovNext(Done, Transition) ≜ 
        ∧ state ∉ Done ∧ Norm(p) ≠ 0
        ∧ ∃ next ∈ DOMAIN Transition[state] : 
            ∧ state' = next 
            ∧ p'     = p ⊙ Transition[state][next]
        

Initial    ≜ "s0"
Accepting  ≜ {"I", "II", "III", "IV", "V", "VI"}
Transition ≜ [s0 ↦ [s1 ↦ 1/2, s2 ↦ 1/2],
               s1 ↦ [s3 ↦ 1/2, s4 ↦ 1/2],
               s2 ↦ [s5 ↦ 1/2, s6 ↦ 1/2],
               s3 ↦ [s1 ↦ 1/2, I  ↦ 1/2],
               s4 ↦ [II ↦ 1/2, III↦ 1/2],
               s5 ↦ [IV ↦ 1/2, V  ↦ 1/2],
               s6 ↦ [VI ↦ 1/2, s2 ↦ 1/2]]
               
Spec ≜ ∧ MarkovInit(Initial) 
       ∧ □[MarkovNext(Accepting, Transition)]_vars 
       ∧ WF_vars(MarkovNext(Accepting, Transition))

THEOREM Converges ≜ Spec ⇒ ◇(state ∈ Accepting ∨ Norm(p) = 0) 
====================================================================================================