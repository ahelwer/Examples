-------------------------------- MODULE Util --------------------------------
EXTENDS Sequences, Functions, Naturals, TLC
\* Simple utility functions
intersects(a, b) ≜ a ∩ b ≠ {}
max(s) ≜ CHOOSE i ∈ s : (¬∃ j ∈ s : j > i)
min(s) ≜ CHOOSE i ∈ s : (¬∃ j ∈ s : j < i)

ReduceSet(op(_, _), set, base) ≜
  LET iter[s ∈ SUBSET set] ≜
        IF s = {} THEN base
        ELSE LET x ≜ CHOOSE x ∈ s: TRUE
             IN  op(x, iter[s \ {x}])
  IN  iter[set]

ReduceSeq(op(_, _), seq, acc) ≜ FoldFunction(op, acc, seq)

Index(seq, e) ≜  CHOOSE i ∈ 1‥Len(seq): seq[i] = e
    
SeqToSet(s) ≜ {s[i] : i ∈ DOMAIN s}
Last(seq) ≜ seq[Len(seq)]
IsEmpty(seq) ≜ Len(seq) = 0
\* Remove all occurrences of `elem` from `seq`
Remove(seq, elem) ≜ SelectSeq(seq, LAMBDA e: e ≠ elem)

\* Dual to UNION on intersect
INTERSECTION(setOfSets) ≜ ReduceSet(∩, setOfSets, UNION setOfSets)

\* Borrowed from Stephan Merz. TLA+ Case Study: A Resource Allocator. [Intern report] A04-R-101 || merz04a, 2004, 20 p. ffinria-00107809f
(* The set of permutations of a finite set, represented as sequences.  *)
PermSeqs(S) ≜
  LET perms[ss ∈ SUBSET S] ≜
       IF ss = {} THEN { ⟨ ⟩ }
       ELSE LET ps ≜ [ x ∈ ss ↦ 
                        { Append(sq,x) : sq ∈ perms[ss \ {x}] } ]
            IN  UNION { ps[x] : x ∈ ss }
  IN  perms[S]

\* Helper to write "unit test" ASSUMES which print when false
test(lhs, rhs) ≜ lhs ≠ rhs ⇒ Print(⟨lhs, " IS NOT ", rhs⟩, FALSE)


=============================================================================
\* Modification History
\* Last modified Sun Aug 05 16:44:44 ET 2023 by murat
\* Created Tue Apr 28 16:43:24 CEST 2020 by tim