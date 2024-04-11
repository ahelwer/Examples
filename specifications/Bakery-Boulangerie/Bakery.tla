------------ MODULE Bakery ----------------------------
(***************************************************************************)
(* The bakery algorithm originally appeared in:                            *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The code for the algorithm given in that paper is :                     *)
(*                                                                      `. *)
(*   begin integer j;                                                      *)
(*   L1: choosing [i] := 1 ;                                               *)
(*       number[i] := 1 + maximum (number[1],..., number[N]);              *)
(*       choosing[i] := 0;                                                 *)
(*       for j = 1 step l until N do                                       *)
(*          begin                                                          *)
(*            L2: if choosing[j] /= 0 then goto L2;                        *)
(*            L3: if number[j] /= 0 and (number [j], j) < (number[i],i)    *)
(*                  then goto L3;                                          *)
(*          end;                                                           *)
(*       critical section;                                                 *)
(*       number[i] := O;                                                   *)
(*       noncritical section;                                              *)
(*       goto L1 ;                                                         *)
(*   end                                                               .'  *)
(*                                                                         *)
(* This PlusCal version of the Atomic Bakery algorithm is one in which     *)
(* variables whose initial values are not used are initialized to          *)
(* particular type-correct values.  If the variables were left             *)
(* uninitialized, the PlusCal translation would initialize them to a       *)
(* particular unspecified value.  This would complicate the proof because  *)
(* it would make the type-correctness invariant more complicated, but it   *)
(* would be efficient to model check.  We could write a version that is    *)
(* more elegant and easy to prove, but less efficient to model check, by   *)
(* initializing the variables to arbitrarily chosen type-correct values.   *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)
CONSTANT N
ASSUME N ∈ ℕ

(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)
Procs ≜ 1‥N 

(***************************************************************************)
(* \prec is defined to be the lexicographical less-than relation on pairs  *)
(* of numbers.                                                             *)
(***************************************************************************)
a ≺ b ≜ ∨ a[1] < b[1]
        ∨ (a[1] = b[1]) ∧ (a[2] < b[2])

(***       this is a comment containing the PlusCal code *

--algorithm Bakery 
{ variables num = [i ∈ Procs ↦ 0], flag = [i ∈ Procs ↦ FALSE];
  fair process (p ∈ Procs)
    variables unchecked = {}, max = 0, nxt = 1 ;
    { ncs:- while (TRUE) 
            { e1:   either { flag[self] ≔ ¬ flag[self] ;
                             goto e1 }
                    or     { flag[self] ≔ TRUE;
                             unchecked ≔ Procs \ {self} ;
                             max ≔ 0
                           } ;     
              e2:   while (unchecked ≠ {}) 
                      { with (i ∈ unchecked) 
                          { unchecked ≔ unchecked \ {i};
                            if (num[i] > max) { max ≔ num[i] }
                          }
                      };
              e3:   either { with (k ∈ ℕ) { num[self] ≔ k } ;
                             goto e3 }
                    or     { with (i ∈ {j ∈ ℕ : j > max}) 
                               { num[self] ≔ i }
                           } ;
              e4:   either { flag[self] ≔ ¬ flag[self] ;
                             goto e4 }
                    or     { flag[self] ≔ FALSE;
                             unchecked ≔ Procs \ {self} 
                           } ;
              w1:   while (unchecked ≠ {}) 
                      {     with (i ∈ unchecked) { nxt ≔ i };
                            await ¬ flag[nxt];
                        w2: await ∨ num[nxt] = 0
                                  ∨ ⟨num[self], self⟩ ≺ ⟨num[nxt], nxt⟩ ;
                            unchecked ≔ unchecked \ {nxt};
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k ∈ ℕ) { num[self] ≔ k } ;
                             goto exit }
                    or     { num[self] ≔ 0 } 
            }
    }
}

    this ends the comment containing the PlusCal code
*************)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)
VARIABLES num, flag, pc, unchecked, max, nxt

vars ≜ ⟨ num, flag, pc, unchecked, max, nxt ⟩

ProcSet ≜ (Procs)

Init ≜ (* Global variables *)
        ∧ num = [i ∈ Procs ↦ 0]
        ∧ flag = [i ∈ Procs ↦ FALSE]
        (* Process p *)
        ∧ unchecked = [self ∈ Procs ↦ {}]
        ∧ max = [self ∈ Procs ↦ 0]
        ∧ nxt = [self ∈ Procs ↦ 1]
        ∧ pc = [self ∈ ProcSet ↦ "ncs"]

ncs(self) ≜ ∧ pc[self] = "ncs"
            ∧ pc' = [pc EXCEPT ![self] = "e1"]
            ∧ UNCHANGED ⟨ num, flag, unchecked, max, nxt ⟩

e1(self) ≜ ∧ pc[self] = "e1"
           ∧ ∨ ∧ flag' = [flag EXCEPT ![self] = ¬ flag[self]]
               ∧ pc' = [pc EXCEPT ![self] = "e1"]
               ∧ UNCHANGED ⟨unchecked, max⟩
             ∨ ∧ flag' = [flag EXCEPT ![self] = TRUE]
               ∧ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               ∧ max' = [max EXCEPT ![self] = 0]
               ∧ pc' = [pc EXCEPT ![self] = "e2"]
           ∧ UNCHANGED ⟨ num, nxt ⟩

e2(self) ≜ ∧ pc[self] = "e2"
           ∧ IF unchecked[self] ≠ {}
                  THEN ∧ ∃ i ∈ unchecked[self]:
                            ∧ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}]
                            ∧ IF num[i] > max[self]
                                  THEN ∧ max' = [max EXCEPT ![self] = num[i]]
                                  ELSE ∧ TRUE
                                       ∧ max' = max
                       ∧ pc' = [pc EXCEPT ![self] = "e2"]
                  ELSE ∧ pc' = [pc EXCEPT ![self] = "e3"]
                       ∧ UNCHANGED ⟨ unchecked, max ⟩
           ∧ UNCHANGED ⟨ num, flag, nxt ⟩

e3(self) ≜ ∧ pc[self] = "e3"
           ∧ ∨ ∧ ∃ k ∈ ℕ:
                       num' = [num EXCEPT ![self] = k]
               ∧ pc' = [pc EXCEPT ![self] = "e3"]
             ∨ ∧ ∃ i ∈ {j ∈ ℕ : j > max[self]}:
                       num' = [num EXCEPT ![self] = i]
               ∧ pc' = [pc EXCEPT ![self] = "e4"]
           ∧ UNCHANGED ⟨ flag, unchecked, max, nxt ⟩

e4(self) ≜ ∧ pc[self] = "e4"
           ∧ ∨ ∧ flag' = [flag EXCEPT ![self] = ¬ flag[self]]
               ∧ pc' = [pc EXCEPT ![self] = "e4"]
               ∧ UNCHANGED unchecked
             ∨ ∧ flag' = [flag EXCEPT ![self] = FALSE]
               ∧ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               ∧ pc' = [pc EXCEPT ![self] = "w1"]
           ∧ UNCHANGED ⟨ num, max, nxt ⟩

w1(self) ≜ ∧ pc[self] = "w1"
           ∧ IF unchecked[self] ≠ {}
                  THEN ∧ ∃ i ∈ unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
                       ∧ ¬ flag[nxt'[self]]
                       ∧ pc' = [pc EXCEPT ![self] = "w2"]
                  ELSE ∧ pc' = [pc EXCEPT ![self] = "cs"]
                       ∧ nxt' = nxt
           ∧ UNCHANGED ⟨ num, flag, unchecked, max ⟩

w2(self) ≜ ∧ pc[self] = "w2"
           ∧ ∨ num[nxt[self]] = 0
             ∨ ⟨num[self], self⟩ ≺ ⟨num[nxt[self]], nxt[self]⟩
           ∧ unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {nxt[self]}]
           ∧ pc' = [pc EXCEPT ![self] = "w1"]
           ∧ UNCHANGED ⟨ num, flag, max, nxt ⟩

cs(self) ≜ ∧ pc[self] = "cs"
           ∧ TRUE
           ∧ pc' = [pc EXCEPT ![self] = "exit"]
           ∧ UNCHANGED ⟨ num, flag, unchecked, max, nxt ⟩

exit(self) ≜ ∧ pc[self] = "exit"
             ∧ ∨ ∧ ∃ k ∈ ℕ:
                         num' = [num EXCEPT ![self] = k]
                 ∧ pc' = [pc EXCEPT ![self] = "exit"]
               ∨ ∧ num' = [num EXCEPT ![self] = 0]
                 ∧ pc' = [pc EXCEPT ![self] = "ncs"]
             ∧ UNCHANGED ⟨ flag, unchecked, max, nxt ⟩

p(self) ≜ ncs(self) ∨ e1(self) ∨ e2(self) ∨ e3(self) ∨ e4(self)
              ∨ w1(self) ∨ w2(self) ∨ cs(self) ∨ exit(self)

Next ≜ (∃ self ∈ Procs: p(self))

Spec ≜ ∧ Init ∧ □[Next]_vars
       ∧ ∀ self ∈ Procs : WF_vars((pc[self] ≠ "ncs") ∧ p(self))

\* END TRANSLATION   (this ends the translation of the PlusCal code)

(***************************************************************************)
(* MutualExclusion asserts that no two distinct processes are in their     *)
(* critical sections.                                                      *)
(***************************************************************************)
MutualExclusion ≜ ∀ i,j ∈ Procs : (i ≠ j) ⇒ ¬ ∧ pc[i] = "cs"
                                              ∧ pc[j] = "cs"
-----------------------------------------------------------------------------
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK ≜ ∧ num ∈ [Procs → ℕ]
         ∧ flag ∈ [Procs → BOOLEAN]
         ∧ unchecked ∈ [Procs → SUBSET Procs]
         ∧ max ∈ [Procs → ℕ]
         ∧ nxt ∈ [Procs → Procs]
         ∧ pc ∈ [Procs → {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]             

(***************************************************************************)
(* Before(i, j) is a condition that implies that num[i] > 0 and, if j is   *)
(* trying to enter its critical section and i does not change num[i], then *)
(* j either has or will choose a value of num[j] for which                 *)
(*                                                                         *)
(*     <<num[i],i>> \prec <<num[j],j>>                                     *)
(*                                                                         *)
(* is true.                                                                *)
(***************************************************************************)
Before(i,j) ≜ ∧ num[i] > 0
              ∧ ∨ pc[j] ∈ {"ncs", "e1", "exit"}
                ∨ ∧ pc[j] = "e2"
                  ∧ ∨ i ∈ unchecked[j]
                    ∨ max[j] ≥ num[i]
                ∨ ∧ pc[j] = "e3"
                  ∧ max[j] ≥ num[i]
                ∨ ∧ pc[j] ∈ {"e4", "w1", "w2"}
                  ∧ ⟨num[i],i⟩ ≺ ⟨num[j],j⟩
                  ∧ (pc[j] ∈ {"w1", "w2"}) ⇒ (i ∈ unchecked[j])


(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
Inv ≜ ∧ TypeOK 
      ∧ ∀ i ∈ Procs : 
\*             /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
             ∧ (pc[i] ∈ {"e4", "w1", "w2", "cs"}) ⇒ (num[i] ≠ 0)
             ∧ (pc[i] ∈ {"e2", "e3"}) ⇒ flag[i] 
             ∧ (pc[i] = "w2") ⇒ (nxt[i] ≠ i)
             ∧ pc[i] ∈ {(*"e2",*) "w1", "w2"} ⇒ i ∉ unchecked[i]
             ∧ (pc[i] ∈ {"w1", "w2"}) ⇒
                   ∀ j ∈ (Procs \ unchecked[i]) \ {i} : Before(i, j)
             ∧ ∧ (pc[i] = "w2")
               ∧ ∨ (pc[nxt[i]] = "e2") ∧ (i ∉ unchecked[nxt[i]])
                 ∨ pc[nxt[i]] = "e3"
               ⇒ max[nxt[i]] ≥ num[i]
             ∧ (pc[i] = "cs") ⇒ ∀ j ∈ Procs \ {i} : Before(i, j)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proof of Mutual Exclusion                                               *)
(*                                                                         *)
(* This is a standard invariance proof, where <1>2 asserts that any step   *)
(* of the algorithm (including a stuttering step) starting in a state in   *)
(* which Inv is true leaves Inv true.  Step <1>4 follows easily from       *)
(* <1>1-<1>3 by simple temporal reasoning.                                 *)
(***************************************************************************)
THEOREM Spec ⇒ □MutualExclusion
<1> USE N ∈ ℕ DEFS Procs, TypeOK, Before, ≺, ProcSet 
<1>1. Init ⇒ Inv
  BY DEF Init, Inv
<1>2. Inv ∧ [Next]_vars ⇒ Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW self ∈ Procs,
               ncs(self)
        PROVE  Inv'
    BY <2>1 DEF ncs, Inv
  <2>2. ASSUME NEW self ∈ Procs,
               e1(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "e1"
         ∧ UNCHANGED ⟨num,nxt⟩
      BY <2>2 DEF e1
    <3>1. CASE ∧ flag' = [flag EXCEPT ![self] = ¬ flag[self]]
               ∧ pc' = [pc EXCEPT ![self] = "e1"]
               ∧ UNCHANGED ⟨unchecked, max⟩
      BY <3>1 DEF Inv
    <3>2. CASE ∧ flag' = [flag EXCEPT ![self] = TRUE]
               ∧ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               ∧ max' = [max EXCEPT ![self] = 0]
               ∧ pc' = [pc EXCEPT ![self] = "e2"]
      BY <3>2 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>2 DEF e1
  <2>3. ASSUME NEW self ∈ Procs,
               e2(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "e2"
         ∧ UNCHANGED ⟨ num, flag, nxt ⟩
      BY <2>3 DEF e2
    <3>1. ASSUME NEW i ∈ unchecked[self],
                 unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
                 num[i] > max[self],
                 max' = [max EXCEPT ![self] = num[i]],
                 pc' = [pc EXCEPT ![self] = "e2"]
          PROVE  Inv'
       BY <3>1, Z3T(10) DEF Inv
    <3>2. ASSUME NEW i ∈ unchecked[self],
                 unchecked' = [unchecked EXCEPT ![self] = unchecked[self] \ {i}],
                 ¬(num[i] > max[self]),
                 max' = max,
                 pc' = [pc EXCEPT ![self] = "e2"]
          PROVE  Inv'
       <4>. TypeOK'  BY <3>2 DEF Inv
       <4>1. ∀ ii ∈ Procs : (pc'[ii] ∈ {"e4", "w1", "w2", "cs"}) ⇒ (num'[ii] ≠ 0)
         BY <3>2 DEF Inv
       <4>2. ∀ ii ∈ Procs : (pc'[ii] ∈ {"e2", "e3"}) ⇒ flag'[ii]
         BY <3>2 DEF Inv
       <4>3. ∀ ii ∈ Procs : (pc'[ii] = "w2") ⇒ (nxt'[ii] ≠ ii)
         BY <3>2 DEF Inv
       <4>4. ∀ ii ∈ Procs : pc'[ii] ∈ {(*"e2",*) "w1", "w2"} ⇒ ii ∉ unchecked'[ii]
         BY <3>2 DEF Inv
       <4>5. ∀ ii ∈ Procs : (pc'[ii] ∈ {"w1", "w2"}) ⇒
                   ∀ j ∈ (Procs \ unchecked'[ii]) \ {ii} : Before(ii, j)'
         BY <3>2 DEF Inv
       <4>6. ∀ ii ∈ Procs : 
                ∧ (pc'[ii] = "w2")
                ∧ ∨ (pc'[nxt'[ii]] = "e2") ∧ (ii ∉ unchecked'[nxt'[ii]])
                  ∨ pc'[nxt'[ii]] = "e3"
                ⇒ max'[nxt'[ii]] ≥ num'[ii]
         BY <3>2 DEF Inv
       <4>7. ∀ ii ∈ Procs : (pc'[ii] = "cs") ⇒ ∀ j ∈ Procs \ {ii} : Before(ii, j)'
         BY <3>2 DEF Inv
       <4>. QED  BY (*<4>0,*) <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7 DEF Inv
    <3>3. CASE ∧ unchecked[self] = {}
               ∧ pc' = [pc EXCEPT ![self] = "e3"]
               ∧ UNCHANGED ⟨ unchecked, max ⟩
       BY <3>3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <3>3, <2>3 DEF e2
  <2>4. ASSUME NEW self ∈ Procs,
               e3(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "e3"
         ∧ UNCHANGED ⟨ flag, unchecked, max, nxt ⟩
      BY <2>4 DEF e3
    <3>1. CASE ∧ ∃ k ∈ ℕ:
                       num' = [num EXCEPT ![self] = k]
               ∧ pc' = [pc EXCEPT ![self] = "e3"]
      BY <3>1 DEF Inv
    <3>2. CASE ∧ ∃ i ∈ {j ∈ ℕ : j > max[self]}:
                       num' = [num EXCEPT ![self] = i]
               ∧ pc' = [pc EXCEPT ![self] = "e4"]
      BY <3>2, SMTT(60) DEF Inv
    <3>3. QED  BY <3>1, <3>2, <2>4 DEF e3
  <2>5. ASSUME NEW self ∈ Procs,
               e4(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "e4"
         ∧ UNCHANGED ⟨ num, max, nxt ⟩
      BY <2>5 DEF e4
    <3>1. CASE ∧ flag' = [flag EXCEPT ![self] = ¬ flag[self]]
               ∧ pc' = [pc EXCEPT ![self] = "e4"]
               ∧ UNCHANGED unchecked
      BY <3>1 DEF Inv
    <3>2. CASE ∧ flag' = [flag EXCEPT ![self] = FALSE]
               ∧ unchecked' = [unchecked EXCEPT ![self] = Procs \ {self}]
               ∧ pc' = [pc EXCEPT ![self] = "w1"]
      BY <3>2, Z3T(30) DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>5 DEF e4
  <2>6. ASSUME NEW self ∈ Procs,
               w1(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "w1"
         ∧ UNCHANGED ⟨ num, flag, unchecked, max ⟩
      BY <2>6 DEF w1
    <3>1. CASE ∧ unchecked[self] ≠ {}
               ∧ ∃ i ∈ unchecked[self]:
                            nxt' = [nxt EXCEPT ![self] = i]
               ∧ ¬ flag[nxt'[self]]
               ∧ pc' = [pc EXCEPT ![self] = "w2"]
      BY <3>1, Z3 DEF Inv
    <3>2. CASE ∧ unchecked[self] = {}
               ∧ pc' = [pc EXCEPT ![self] = "cs"]
               ∧ nxt' = nxt
      BY <3>2, Z3 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>6 DEF w1
  <2>7. ASSUME NEW self ∈ Procs,
               w2(self)
        PROVE  Inv'
    BY <2>7, Z3T(30) DEF w2, Inv
  <2>8. ASSUME NEW self ∈ Procs,
               cs(self)
        PROVE  Inv'
    BY <2>8, Z3 DEF cs, Inv
  <2>9. ASSUME NEW self ∈ Procs,
               exit(self)
        PROVE  Inv'
    <3>. ∧ pc[self] = "exit"
         ∧ UNCHANGED ⟨ flag, unchecked, max, nxt ⟩
      BY <2>9 DEF exit
    <3>1. CASE ∧ ∃ k ∈ ℕ:
                         num' = [num EXCEPT ![self] = k]
               ∧ pc' = [pc EXCEPT ![self] = "exit"]
      BY <3>1 DEF Inv
    <3>2. CASE ∧ num' = [num EXCEPT ![self] = 0]
               ∧ pc' = [pc EXCEPT ![self] = "ncs"]
      BY <3>2 DEF Inv
    <3>. QED  BY <3>1, <3>2, <2>9 DEF exit
  <2>10. CASE UNCHANGED vars
    BY <2>10 DEF vars, Inv
  <2>11. QED
    BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Next, p
<1>3. Inv ⇒ MutualExclusion
  BY SMT DEF MutualExclusion, Inv
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec
------------------------------------------------------------------------------ 
Trying(i) ≜ pc[i] = "e1"
InCS(i)   ≜ pc[i] = "cs"
DeadlockFree ≜ (∃ i ∈ Procs : Trying(i)) ↝ (∃ i ∈ Procs : InCS(i))
StarvationFree ≜ ∀ i ∈ Procs : Trying(i) ↝ InCS(i)

-----------------------------------------------------------------------------
II ≜ ∀ i ∈ Procs : 
\*        /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)             \* not found Test 1 (21993 states)
        ∧ (pc[i] ∈ {"e4", "w1", "w2", "cs"}) ⇒ (num[i] ≠ 0)        \* found Test 1
        ∧ (pc[i] ∈ {"e2", "e3"}) ⇒ flag[i]                         \* found Test 1
        ∧ (pc[i] = "w2") ⇒ (nxt[i] ≠ i)                              \* not found Test 1 (12115 states) or with N=2
        ∧ pc[i] ∈ {"e2", "w1", "w2"} ⇒ i ∉ unchecked[i]       \* found Test 1 
        ∧ (pc[i] ∈ {"w1", "w2"}) ⇒                                 \* found Test 1
              ∀ j ∈ (Procs \ unchecked[i]) \ {i} : Before(i, j)
        ∧ ∧ (pc[i] = "w2")                                           \* found Test 1
          ∧ ∨ (pc[nxt[i]] = "e2") ∧ (i ∉ unchecked[nxt[i]])
            ∨ pc[nxt[i]] = "e3"
          ⇒ max[nxt[i]] ≥ num[i]
        ∧ (pc[i] = "cs") ⇒ ∀ j ∈ Procs \ {i} : Before(i, j)     \* found Test 1
             
IInit ≜ ∧ num ∈ [Procs → ℕ]
        ∧ flag ∈ [Procs → BOOLEAN]
        ∧ unchecked ∈ [Procs → SUBSET Procs]
        ∧ max ∈ [Procs →  ℕ]
        ∧ nxt ∈ [Procs →  Procs]
        ∧ pc ∈ [Procs → {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}] 
        ∧ II  

ISpec ≜ IInit ∧ □[Next]_vars
             
=============================================================================
\* Modification History
\* Last modified Mon Mar 06 13:47:10 CET 2023 by merz
\* Last modified Tue Aug 27 12:23:10 PDT 2019 by loki
\* Last modified Sat May 19 16:40:23 CEST 2018 by merz
\* Last modified Thu May 17 07:02:45 PDT 2018 by lamport
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport

Test 1:  5248 distinct initial states  151056 full initial states
IInit == /\ num \in [Procs -> Nat]
         /\ flag \in [Procs -> BOOLEAN]
         /\ unchecked \in [Procs -> SUBSET Procs]
         /\ max \in [Procs ->  {0}] \* Nat]
         /\ nxt \in [Procs ->  {1}]
         /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs"}] 
         /\ II  