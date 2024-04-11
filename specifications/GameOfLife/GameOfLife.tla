----------------------------- MODULE GameOfLife -----------------------------
EXTENDS Integers

CONSTANT N
VARIABLE grid

ASSUME N ∈ ℕ

vars ≜ grid

RECURSIVE Sum(_, _)
Sum(f, S) ≜ IF S = {} THEN 0
                       ELSE LET x ≜ CHOOSE x ∈ S : TRUE
                            IN  f[x] + Sum(f, S \ {x})
                            
Pos ≜ {⟨x, y⟩ : x, y ∈ 1‥N}
TypeOK ≜ grid ∈ [Pos → BOOLEAN]

sc[⟨x, y⟩ ∈ (0 ‥ N + 1) ×
                (0 ‥ N + 1)] ≜ CASE ∨ x = 0 ∨ y = 0
                                    ∨ x > N ∨ y > N
                                    ∨ ¬grid[⟨x, y⟩] → 0
                                   □ OTHER → 1

score(p) ≜ LET nbrs ≜ {x ∈ {-1, 0, 1} ×
                               {-1, 0, 1} : x ≠ ⟨0, 0⟩}
                points ≜ {⟨p[1] + x, p[2] + y⟩ : ⟨x, y⟩ ∈ nbrs}
            IN Sum(sc, points)
                   
Init ≜ grid ∈ [Pos → BOOLEAN]
Next ≜ grid' = [p ∈ Pos ↦ IF ∨  (grid[p] ∧ score(p) ∈ {2, 3})
                             ∨ (¬grid[p] ∧ score(p) = 3)
                                THEN TRUE
                                ELSE FALSE]

Spec ≜ Init ∧ □[Next]_vars

=============================================================================