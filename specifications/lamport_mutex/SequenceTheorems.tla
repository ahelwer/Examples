----------------------- MODULE SequenceTheorems -----------------------------
(***************************************************************************)
(* This module contains a library of theorems about sequences and the      *)
(* corresponding operations.                                               *)
(***************************************************************************)
EXTENDS Sequences, Integers, WellFoundedInduction, Functions, TLAPS


(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

LEMMA SeqDef ≜ ∀ S : Seq(S) = UNION {[1‥n → S] : n ∈ ℕ}

THEOREM ElementOfSeq ≜
   ASSUME NEW S, NEW seq ∈ Seq(S),
          NEW n ∈ 1‥Len(seq)
   PROVE  seq[n] ∈ S
 
THEOREM EmptySeq ≜
   ASSUME NEW S
   PROVE ∧ ⟨ ⟩ ∈ Seq(S)
         ∧ ∀ seq ∈ Seq(S) : (seq = ⟨ ⟩) ⇔ (Len(seq) = 0)

THEOREM LenProperties ≜ 
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  ∧ Len(seq) ∈ ℕ
         ∧ seq ∈ [1‥Len(seq) → S]
         ∧ DOMAIN seq = 1 ‥ Len(seq) 

THEOREM ExceptSeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW i ∈ 1 ‥ Len(seq), NEW e ∈ S
  PROVE  ∧ [seq EXCEPT ![i] = e] ∈ Seq(S)
         ∧ Len([seq EXCEPT ![i] = e]) = Len(seq)
         ∧ ∀ j ∈ 1 ‥ Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]

THEOREM IsASeq ≜
  ASSUME NEW n ∈ ℕ, NEW e(_), NEW S,
         ∀ i ∈ 1‥n : e(i) ∈ S
  PROVE  [i ∈ 1‥n ↦ e(i)] ∈ Seq(S)

THEOREM SeqEqual ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S),
         Len(s) = Len(t), ∀ i ∈ 1 ‥ Len(s) : s[i] = t[i]
  PROVE  s = t

(***************************************************************************
                 Concatenation (\o) And Properties                      
***************************************************************************)

THEOREM ConcatProperties ≜
  ASSUME NEW S, NEW s1 ∈ Seq(S), NEW s2 ∈ Seq(S)
  PROVE  ∧ s1 ∘ s2 ∈ Seq(S)
         ∧ Len(s1 ∘ s2) = Len(s1) + Len(s2)
         ∧ ∀ i ∈ 1 ‥ Len(s1) + Len(s2) : (s1 ∘ s2)[i] =
                     IF i ≤ Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]

THEOREM ConcatEmptySeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  ∧ seq ∘ ⟨ ⟩ = seq
         ∧ ⟨ ⟩ ∘ seq = seq

THEOREM ConcatAssociative ≜
  ASSUME NEW S, NEW s1 ∈ Seq(S), NEW s2 ∈ Seq(S), NEW s3 ∈ Seq(S)
  PROVE  (s1 ∘ s2) ∘ s3 = s1 ∘ (s2 ∘ s3)

THEOREM ConcatSimplifications ≜
  ASSUME NEW S
  PROVE  ∧ ∀ s,t ∈ Seq(S) : s ∘ t = s ⇔ t = ⟨⟩
         ∧ ∀ s,t ∈ Seq(S) : s ∘ t = t ⇔ s = ⟨⟩
         ∧ ∀ s,t ∈ Seq(S) : s ∘ t = ⟨⟩ ⇔ s = ⟨⟩ ∧ t = ⟨⟩
         ∧ ∀ s,t,u ∈ Seq(S) : s ∘ t = s ∘ u ⇔ t = u
         ∧ ∀ s,t,u ∈ Seq(S) : s ∘ u = t ∘ u ⇔ s = t

(***************************************************************************)
(*                     SubSeq, Head and Tail                               *)
(***************************************************************************)

THEOREM SubSeqProperties ≜
  ASSUME NEW S,
         NEW s ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(s)+1,
         NEW n ∈ m-1 ‥ Len(s)
  PROVE  ∧ SubSeq(s,m,n) ∈ Seq(S)
         ∧ Len(SubSeq(s, m, n)) = n-m+1
         ∧ ∀ i ∈ 1 ‥ n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]

THEOREM SubSeqEmpty ≜
  ASSUME NEW s, NEW m ∈ ℤ, NEW n ∈ ℤ, n < m
  PROVE  SubSeq(s,m,n) = ⟨ ⟩

THEOREM HeadTailProperties ≜
   ASSUME NEW S,
          NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
   PROVE  ∧ Head(seq) ∈ S
          ∧ Tail(seq) ∈ Seq(S)
          ∧ Len(Tail(seq)) = Len(seq)-1
          ∧ ∀ i ∈ 1 ‥ Len(Tail(seq)) : Tail(seq)[i] = seq[i+1]

THEOREM TailIsSubSeq ≜
  ASSUME NEW S,
         NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE  Tail(seq) = SubSeq(seq, 2, Len(seq))

THEOREM SubSeqRestrict ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW n ∈ 0 ‥ Len(seq)
  PROVE  SubSeq(seq, 1, n) = Restrict(seq, 1 ‥ n)

THEOREM HeadTailOfSubSeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(seq), NEW n ∈ m ‥ Len(seq)
  PROVE  ∧ Head(SubSeq(seq,m,n)) = seq[m]
         ∧ Tail(SubSeq(seq,m,n)) = SubSeq(seq, m+1, n)

THEOREM SubSeqRecursiveFirst ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(seq), NEW n ∈ m ‥ Len(seq)
  PROVE  SubSeq(seq, m, n) = ⟨ seq[m] ⟩ ∘ SubSeq(seq, m+1, n)

THEOREM SubSeqRecursiveSecond ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(seq), NEW n ∈ m ‥ Len(seq)
  PROVE  SubSeq(seq, m, n) = SubSeq(seq, m, n-1) ∘ ⟨ seq[n] ⟩

LEMMA SubSeqOfSubSeq ≜
  ASSUME NEW S, NEW s ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(s)+1,
         NEW n ∈ m-1 ‥ Len(s),
         NEW i ∈ 1 ‥ n-m+2,
         NEW j ∈ i-1 ‥ n-m+1
  PROVE  SubSeq( SubSeq(s,m,n), i, j ) = SubSeq(s, m+i-1, m+j-1)

THEOREM SubSeqFull ≜
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  SubSeq(seq, 1, Len(seq)) = seq

(*****************************************************************************)
(* Adjacent subsequences can be concatenated to obtain a longer subsequence. *)
(*****************************************************************************)
THEOREM ConcatAdjacentSubSeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), 
         NEW m ∈ 1 ‥ Len(seq)+1, 
         NEW k ∈ m-1 ‥ Len(seq), 
         NEW n ∈ k ‥ Len(seq)
  PROVE  SubSeq(seq, m, k) ∘ SubSeq(seq, k+1, n) = SubSeq(seq, m, n)

(***************************************************************************)
(*                 Append, InsertAt, Cons & RemoveAt                       *)
(* Append(seq, elt) appends element elt at the end of sequence seq         *)
(* Cons(elt, seq) prepends element elt at the beginning of sequence seq    *)
(* InsertAt(seq, i, elt) inserts element elt in the position i and pushes  *)
(* the                                                                     *)
(*                        original element at i to i+1 and so on           *)
(* RemoveAt(seq, i) removes the element at position i                      *)
(***************************************************************************)

THEOREM AppendProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW elt ∈ S
  PROVE  ∧ Append(seq, elt) ∈ Seq(S)
         ∧ Append(seq, elt) ≠ ⟨ ⟩
         ∧ Len(Append(seq, elt)) = Len(seq)+1
         ∧ ∀ i ∈ 1‥ Len(seq) : Append(seq, elt)[i] = seq[i]
         ∧ Append(seq, elt)[Len(seq)+1] = elt

THEOREM AppendIsConcat ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW elt ∈ S
  PROVE  Append(seq, elt) = seq ∘ ⟨elt⟩

THEOREM HeadTailAppend ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW elt
  PROVE  ∧ Head(Append(seq, elt)) = IF seq = ⟨⟩ THEN elt ELSE Head(seq)
         ∧ Tail(Append(seq, elt)) = IF seq = ⟨⟩ THEN ⟨⟩ ELSE Append(Tail(seq), elt)

Cons(elt, seq) ≜ ⟨elt⟩ ∘ seq

THEOREM ConsProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW elt ∈ S
  PROVE ∧ Cons(elt, seq) ∈ Seq(S)
        ∧ Cons(elt, seq) ≠ ⟨⟩ 
        ∧ Len(Cons(elt, seq)) = Len(seq)+1
        ∧ Head(Cons(elt, seq)) = elt
        ∧ Tail(Cons(elt, seq)) = seq
        ∧ Cons(elt, seq)[1] = elt
        ∧ ∀ i ∈ 1 ‥ Len(seq) : Cons(elt, seq)[i+1] = seq[i]

THEOREM ConsEmpty ≜
  ∀ x : Cons(x, ⟨ ⟩) = ⟨ x ⟩

THEOREM ConsHeadTail ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE  Cons(Head(seq), Tail(seq)) = seq

THEOREM ConsAppend ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW x ∈ S, NEW y ∈ S
  PROVE  Cons(x, Append(seq, y)) = Append(Cons(x,seq), y)

THEOREM ConsInjective ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW f ∈ S, NEW t ∈ Seq(S)
  PROVE  Cons(e,s) = Cons(f,t) ⇔ e = f ∧ s = t

InsertAt(seq,i,elt) ≜ SubSeq(seq, 1, i-1) ∘ ⟨elt⟩ ∘ SubSeq(seq, i, Len(seq))

THEOREM InsertAtProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW i ∈ 1 ‥ Len(seq)+1, NEW elt ∈ S
  PROVE  ∧ InsertAt(seq,i,elt) ∈ Seq(S)
         ∧ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         ∧ ∀ j ∈ 1 ‥ Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]

RemoveAt(seq, i) ≜ SubSeq(seq, 1, i-1) ∘ SubSeq(seq, i+1, Len(seq))

THEOREM RemoveAtProperties ≜
   ASSUME NEW S, NEW seq ∈ Seq(S),
          NEW i ∈ 1‥Len(seq)
   PROVE  ∧ RemoveAt(seq,i) ∈ Seq(S)
          ∧ Len(RemoveAt(seq,i)) = Len(seq) - 1
          ∧ ∀ j ∈ 1 ‥ Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]

(***************************************************************************)
(*            Front & Last                                                 *)
(*                                                                         *)
(*  Front(seq)   sequence formed by removing the last element              *)
(*  Last(seq)    last element of the sequence                              *)
(*                                                                         *)
(*  These operators are to Append what Head and Tail are to Cons.          *)
(***************************************************************************)

Front(seq) ≜ SubSeq(seq, 1, Len(seq)-1)
Last(seq) ≜ seq[Len(seq)]

THEOREM FrontProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  ∧ Front(seq) ∈ Seq(S)
         ∧ Len(Front(seq)) = IF seq = ⟨ ⟩ THEN 0 ELSE Len(seq)-1                    
         ∧ ∀ i ∈ 1 ‥ Len(seq)-1 : Front(seq)[i] = seq[i]

THEOREM FrontOfEmpty ≜ Front(⟨ ⟩) = ⟨ ⟩

THEOREM LastProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE  ∧ Last(seq) ∈ S 
         ∧ Append(Front(seq), Last(seq)) = seq 

THEOREM FrontLastOfSubSeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         NEW m ∈ 1 ‥ Len(seq), NEW n ∈ m ‥ Len(seq)
  PROVE  ∧ Front(SubSeq(seq,m,n)) = SubSeq(seq, m, n-1)
         ∧ Last(SubSeq(seq,m,n)) = seq[n]

THEOREM FrontLastAppend ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW e ∈ S
  PROVE  ∧ Front(Append(seq, e)) = seq
         ∧ Last(Append(seq, e)) = e

THEOREM AppendInjective ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW f ∈ S, NEW t ∈ Seq(S)
  PROVE  Append(s,e) = Append(t,f) ⇔ s = t ∧ e = f

(***************************************************************************)
(* As a corollary of the previous theorems it follows that a sequence is   *)
(* either empty or can be obtained by appending an element to a sequence.  *)
(***************************************************************************)
THEOREM SequenceEmptyOrAppend ≜ 
  ASSUME NEW S, NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE ∃ s ∈ Seq(S), elt ∈ S : seq = Append(s, elt)
     
(***************************************************************************)
(*                   REVERSE SEQUENCE And Properties                       *)
(*    Reverse(seq) --> Reverses the sequence seq                           *)
(***************************************************************************)

Reverse(seq) ≜ [j ∈ 1 ‥ Len(seq) ↦ seq[Len(seq)-j+1] ]

THEOREM ReverseProperties ≜
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  ∧ Reverse(seq) ∈ Seq(S)
         ∧ Len(Reverse(seq)) = Len(seq)
         ∧ Reverse(Reverse(seq)) = seq

THEOREM ReverseEmpty ≜ Reverse(⟨ ⟩) = ⟨ ⟩

THEOREM ReverseEqual ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), Reverse(s) = Reverse(t)
  PROVE  s = t

THEOREM ReverseEmptyIffEmpty ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), Reverse(seq) = ⟨⟩
  PROVE  seq = ⟨⟩

THEOREM ReverseConcat ≜ 
  ASSUME NEW S, NEW s1 ∈ Seq(S), NEW s2 ∈ Seq(S)
  PROVE  Reverse(s1 ∘ s2) = Reverse(s2) ∘ Reverse(s1)

THEOREM ReverseAppend ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW e ∈ S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))

THEOREM ReverseCons ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), NEW e ∈ S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)

THEOREM ReverseSingleton ≜ ∀ x : Reverse(⟨ x ⟩) = ⟨ x ⟩

THEOREM ReverseSubSeq ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         NEW m ∈ 1‥Len(seq), NEW n ∈ 1‥Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)

THEOREM ReversePalindrome ≜
  ASSUME NEW S, NEW seq ∈ Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq ∘ seq) = seq ∘ seq

THEOREM LastEqualsHeadReverse ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE  Last(seq) = Head(Reverse(seq))

THEOREM ReverseFrontEqualsTailReverse ≜
  ASSUME NEW S, NEW seq ∈ Seq(S), seq ≠ ⟨ ⟩
  PROVE  Reverse(Front(seq)) = Tail(Reverse(seq))

(***************************************************************************)
(* Induction principles for sequences                                      *)
(***************************************************************************)

THEOREM SequencesInductionAppend ≜
  ASSUME NEW P(_), NEW S, 
         P(⟨ ⟩),
         ∀ s ∈ Seq(S), e ∈ S : P(s) ⇒ P(Append(s,e))
  PROVE  ∀ seq ∈ Seq(S) : P(seq)
      
THEOREM SequencesInductionCons ≜ 
  ASSUME NEW P(_), NEW S,
         P(⟨ ⟩),
         ∀ s ∈ Seq(S), e ∈ S : P(s) ⇒ P(Cons(e,s))
  PROVE ∀ seq ∈ Seq(S) : P(seq)

(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

THEOREM RangeOfSeq ≜ 
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE  Range(seq) ∈ SUBSET S

THEOREM RangeEquality ≜ 
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE Range(seq) = { seq[i] : i ∈ 1 ‥ Len(seq) }

(* The range of the reverse sequence equals that of the original one. *)
THEOREM RangeReverse ≜ 
  ASSUME NEW S, NEW seq ∈ Seq(S)
  PROVE Range(Reverse(seq)) = Range(seq)

(* Range of concatenation of sequences is the union of the ranges *)
THEOREM RangeConcatenation ≜ 
  ASSUME NEW S, NEW s1 ∈ Seq(S), NEW s2 ∈ Seq(S)
  PROVE  Range(s1 ∘ s2) = Range(s1) ∪ Range(s2)

(***************************************************************************)
(* Prefixes and suffixes of sequences.                                     *)
(***************************************************************************)

IsPrefix(s,t) ≜ ∃ u ∈ Seq(Range(t)) : t = s ∘ u
IsStrictPrefix(s,t) ≜ IsPrefix(s,t) ∧ s ≠ t

IsSuffix(s,t) ≜ ∃ u ∈ Seq(Range(t)) : t = u ∘ s
IsStrictSuffix(s,t) ≜ IsSuffix(s,t) ∧ s ≠ t

(***************************************************************************)
(* The following theorem gives three alternative characterizations of      *)
(* prefixes. It also implies that any prefix of a sequence t is at most    *)
(* as long as t.                                                           *)
(***************************************************************************)
THEOREM IsPrefixProperties ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  ∧ IsPrefix(s,t) ⇔ ∃ u ∈ Seq(S) : t = s ∘ u
         ∧ IsPrefix(s,t) ⇔ Len(s) ≤ Len(t) ∧ s = SubSeq(t, 1, Len(s))
         ∧ IsPrefix(s,t) ⇔ Len(s) ≤ Len(t) ∧ s = Restrict(t, DOMAIN s)

THEOREM IsStrictPrefixProperties ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  ∧ IsStrictPrefix(s,t) ⇔ ∃ u ∈ Seq(S) : u ≠ ⟨ ⟩ ∧ t = s ∘ u
         ∧ IsStrictPrefix(s,t) ⇔ Len(s) < Len(t) ∧ s = SubSeq(t, 1, Len(s))
         ∧ IsStrictPrefix(s,t) ⇔ Len(s) < Len(t) ∧ s = Restrict(t, DOMAIN s)
         ∧ IsStrictPrefix(s,t) ⇔ IsPrefix(s,t) ∧ Len(s) < Len(t)

THEOREM IsPrefixElts ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW i ∈ 1 ‥ Len(s),
         IsPrefix(s,t)
  PROVE  s[i] = t[i]

THEOREM EmptyIsPrefix ≜
  ASSUME NEW S, NEW s ∈ Seq(S)
  PROVE  ∧ IsPrefix(⟨⟩, s)
         ∧ IsPrefix(s, ⟨⟩) ⇔ s = ⟨⟩
         ∧ IsStrictPrefix(⟨⟩, s) ⇔ s ≠ ⟨⟩
         ∧ ¬ IsStrictPrefix(s, ⟨⟩)

THEOREM IsPrefixConcat ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  IsPrefix(s, s ∘ t)

THEOREM IsPrefixAppend ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW e ∈ S
  PROVE  IsPrefix(s, Append(s,e))

THEOREM FrontIsPrefix ≜
  ASSUME NEW S, NEW s ∈ Seq(S)
  PROVE  ∧ IsPrefix(Front(s), s)
         ∧ s ≠ ⟨⟩ ⇒ IsStrictPrefix(Front(s), s)

LEMMA RangeIsPrefix ≜ 
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S),
         IsPrefix(s,t)
  PROVE Range(s) ⊆ Range(t)

LEMMA IsPrefixMap ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), IsPrefix(s,t),
         NEW Op(_)
  PROVE  IsPrefix([i ∈ DOMAIN s ↦ Op(s[i])],
                  [i ∈ DOMAIN t ↦ Op(t[i])])

(***************************************************************************)
(* (Strict) prefixes on sequences form a (strict) partial order, and       *)
(* the strict ordering is well-founded.                                    *)
(***************************************************************************)
THEOREM IsPrefixPartialOrder ≜
  ASSUME NEW S
  PROVE  ∧ ∀ s ∈ Seq(S) : IsPrefix(s,s)
         ∧ ∀ s,t ∈ Seq(S) : IsPrefix(s,t) ∧ IsPrefix(t,s) ⇒ s = t
         ∧ ∀ s,t,u ∈ Seq(S) : IsPrefix(s,t) ∧ IsPrefix(t,u) ⇒ IsPrefix(s,u)

THEOREM ConcatIsPrefix ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW u ∈ Seq(S),
         IsPrefix(s ∘ t, u)
  PROVE  IsPrefix(s, u)

THEOREM ConcatIsPrefixCancel ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW u ∈ Seq(S)
  PROVE  IsPrefix(s ∘ t, s ∘ u) ⇔ IsPrefix(t, u)

THEOREM ConsIsPrefixCancel ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  IsPrefix(Cons(e,s), Cons(e,t)) ⇔ IsPrefix(s,t)

THEOREM ConsIsPrefix ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW u ∈ Seq(S),
         IsPrefix(Cons(e,s), u)
  PROVE  ∧ e = Head(u)
         ∧ IsPrefix(s, Tail(u))

THEOREM IsStrictPrefixStrictPartialOrder ≜
  ASSUME NEW S
  PROVE  ∧ ∀ s ∈ Seq(S) : ¬ IsStrictPrefix(s,s)
         ∧ ∀ s,t ∈ Seq(S) : IsStrictPrefix(s,t) ⇒ ¬ IsStrictPrefix(t,s)
         ∧ ∀ s,t,u ∈ Seq(S) : IsStrictPrefix(s,t) ∧ IsStrictPrefix(t,u) ⇒ IsStrictPrefix(s,u)

THEOREM IsStrictPrefixWellFounded ≜
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))

THEOREM SeqStrictPrefixInduction ≜
  ASSUME NEW P(_), NEW S,
         ∀ t ∈ Seq(S) : (∀ s ∈ Seq(S) : IsStrictPrefix(s,t) ⇒ P(s)) ⇒ P(t)
  PROVE  ∀ s ∈ Seq(S) : P(s)

(***************************************************************************)
(* Similar theorems about suffixes.                                        *)
(***************************************************************************)

THEOREM IsSuffixProperties ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  ∧ IsSuffix(s,t) ⇔ ∃ u ∈ Seq(S) : t = u ∘ s
         ∧ IsSuffix(s,t) ⇔ Len(s) ≤ Len(t) ∧ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         ∧ IsSuffix(s,t) ⇔ IsPrefix(Reverse(s), Reverse(t))

THEOREM IsStrictSuffixProperties ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  ∧ IsStrictSuffix(s,t) ⇔ ∃ u ∈ Seq(S) : u ≠ ⟨ ⟩ ∧ t = u ∘ s
         ∧ IsStrictSuffix(s,t) ⇔ Len(s) < Len(t) ∧ IsSuffix(s,t)
         ∧ IsStrictSuffix(s,t) ⇔ Len(s) < Len(t) ∧ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         ∧ IsStrictSuffix(s,t) ⇔ IsStrictPrefix(Reverse(s), Reverse(t))

THEOREM IsSuffixElts ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW i ∈ 1 ‥ Len(s),
         IsSuffix(s,t)
  PROVE  s[i] = t[Len(t) - Len(s) + i]

THEOREM EmptyIsSuffix ≜
  ASSUME NEW S, NEW s ∈ Seq(S)
  PROVE  ∧ IsSuffix(⟨⟩, s)
         ∧ IsSuffix(s, ⟨⟩) ⇔ s = ⟨⟩
         ∧ IsStrictSuffix(⟨⟩, s) ⇔ s ≠ ⟨⟩
         ∧ ¬ IsStrictSuffix(s, ⟨⟩)

THEOREM IsSuffixConcat ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  IsSuffix(s, t ∘ s)

THEOREM IsStrictSuffixCons ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW e ∈ S
  PROVE  IsStrictSuffix(s, Cons(e,s))

THEOREM TailIsSuffix ≜
  ASSUME NEW S, NEW s ∈ Seq(S)
  PROVE  ∧ IsSuffix(Tail(s), s)
         ∧ s ≠ ⟨⟩ ⇒ IsStrictSuffix(Tail(s), s)

THEOREM IsSuffixPartialOrder ≜
  ASSUME NEW S
  PROVE  ∧ ∀ s ∈ Seq(S) : IsSuffix(s,s)
         ∧ ∀ s,t ∈ Seq(S) : IsSuffix(s,t) ∧ IsSuffix(t,s) ⇒ s = t
         ∧ ∀ s,t,u ∈ Seq(S) : IsSuffix(s,t) ∧ IsSuffix(t,u) ⇒ IsSuffix(s,u)

THEOREM ConcatIsSuffix ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW u ∈ Seq(S),
         IsSuffix(s ∘ t, u)
  PROVE  IsSuffix(t, u)

THEOREM ConcatIsSuffixCancel ≜
  ASSUME NEW S, NEW s ∈ Seq(S), NEW t ∈ Seq(S), NEW u ∈ Seq(S)
  PROVE  IsSuffix(s ∘ t, u ∘ t) ⇔ IsSuffix(s, u)

THEOREM AppendIsSuffixCancel ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW t ∈ Seq(S)
  PROVE  IsSuffix(Append(s,e), Append(t,e)) ⇔ IsSuffix(s,t)

THEOREM AppendIsSuffix ≜
  ASSUME NEW S, NEW e ∈ S, NEW s ∈ Seq(S), NEW u ∈ Seq(S),
         IsSuffix(Append(s,e), u)
  PROVE  ∧ e = Last(u)
         ∧ IsSuffix(s, Front(u))

THEOREM IsStrictSuffixStrictPartialOrder ≜
  ASSUME NEW S
  PROVE  ∧ ∀ s ∈ Seq(S) : ¬ IsStrictSuffix(s,s)
         ∧ ∀ s,t ∈ Seq(S) : IsStrictSuffix(s,t) ⇒ ¬ IsStrictSuffix(t,s)
         ∧ ∀ s,t,u ∈ Seq(S) : IsStrictSuffix(s,t) ∧ IsStrictSuffix(t,u) ⇒ IsStrictSuffix(s,u)

THEOREM IsStrictSuffixWellFounded ≜
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))

THEOREM SeqStrictSuffixInduction ≜
  ASSUME NEW P(_), NEW S,
         ∀ t ∈ Seq(S) : (∀ s ∈ Seq(S) : IsStrictSuffix(s,t) ⇒ P(s)) ⇒ P(t)
  PROVE  ∀ s ∈ Seq(S) : P(s)

(***************************************************************************)
(* Since the (strict) prefix and suffix orderings on sequences are         *)
(* well-founded, they can be used for defining recursive functions.        *)
(* The operators OpDefinesFcn, WFInductiveDefines, and WFInductiveUnique   *)
(* are defined in module WellFoundedInduction.                             *)
(***************************************************************************)

StrictPrefixesDetermineDef(S, Def(_,_)) ≜
   ∀ g,h : ∀ seq ∈ Seq(S) :
      (∀ pre ∈ Seq(S) : IsStrictPrefix(pre,seq) ⇒ g[pre] = h[pre])
      ⇒ Def(g, seq) = Def(h, seq)

LEMMA StrictPrefixesDetermineDef_WFDefOn ≜
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionUnique ≜
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionDef ≜
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictPrefixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionType ≜
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T ≠ {},
         StrictPrefixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         ∀ g ∈ [Seq(S) → T], s ∈ Seq(S) : Def(g,s) ∈ T
  PROVE  f ∈ [Seq(S) → T]

StrictSuffixesDetermineDef(S, Def(_,_)) ≜
   ∀ g,h : ∀ seq ∈ Seq(S) :
      (∀ suf ∈ Seq(S) : IsStrictSuffix(suf,seq) ⇒ g[suf] = h[suf])
      ⇒ Def(g, seq) = Def(h, seq)

LEMMA StrictSuffixesDetermineDef_WFDefOn ≜
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionUnique ≜
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionDef ≜
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictSuffixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionType ≜
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T ≠ {},
         StrictSuffixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         ∀ g ∈ [Seq(S) → T], s ∈ Seq(S) : Def(g,s) ∈ T
  PROVE  f ∈ [Seq(S) → T]

(***************************************************************************)
(* The following theorems justify ``primitive recursive'' functions over   *)
(* sequences, with a base case for the empty sequence and recursion along  *)
(* either the Tail or the Front of a non-empty sequence.                   *)
(***************************************************************************)

TailInductiveDefHypothesis(f, S, f0, Def(_,_)) ≜
  f = CHOOSE g : g = [s ∈ Seq(S) ↦ IF s = ⟨⟩ THEN f0 ELSE Def(g[Tail(s)], s)]

TailInductiveDefConclusion(f, S, f0, Def(_,_)) ≜
  f = [s ∈ Seq(S) ↦ IF s = ⟨⟩ THEN f0 ELSE Def(f[Tail(s)], s)]

THEOREM TailInductiveDef ≜
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         TailInductiveDefHypothesis(f, S, f0, Def)
  PROVE  TailInductiveDefConclusion(f, S, f0, Def)

THEOREM TailInductiveDefType ≜
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         TailInductiveDefConclusion(f, S, f0, Def),
         f0 ∈ T,
         ∀ v ∈ T, s ∈ Seq(S) : s ≠ ⟨⟩ ⇒ Def(v,s) ∈ T
  PROVE  f ∈ [Seq(S) → T]

FrontInductiveDefHypothesis(f, S, f0, Def(_,_)) ≜
  f = CHOOSE g : g = [s ∈ Seq(S) ↦ IF s = ⟨⟩ THEN f0 ELSE Def(g[Front(s)], s)]

FrontInductiveDefConclusion(f, S, f0, Def(_,_)) ≜
  f = [s ∈ Seq(S) ↦ IF s = ⟨⟩ THEN f0 ELSE Def(f[Front(s)], s)]

THEOREM FrontInductiveDef ≜
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         FrontInductiveDefHypothesis(f, S, f0, Def)
  PROVE  FrontInductiveDefConclusion(f, S, f0, Def)

THEOREM FrontInductiveDefType ≜
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         FrontInductiveDefConclusion(f, S, f0, Def),
         f0 ∈ T,
         ∀ v ∈ T, s ∈ Seq(S) : s ≠ ⟨⟩ ⇒ Def(v,s) ∈ T
  PROVE  f ∈ [Seq(S) → T]

=============================================================================