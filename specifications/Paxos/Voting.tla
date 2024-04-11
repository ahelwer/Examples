------------------------------- MODULE Voting ------------------------------- 
(***************************************************************************)
(* This is a high-level algorithm in which a set of processes              *)
(* cooperatively choose a value.                                           *)
(***************************************************************************)
EXTENDS Integers, TLAPS
-----------------------------------------------------------------------------
CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors

(***************************************************************************)
(* Here are the assumptions we make about quorums.                         *)
(***************************************************************************)
ASSUME QuorumAssumption ≜ ∧ ∀ Q ∈ Quorum : Q ⊆ Acceptor
                          ∧ ∀ Q1, Q2 ∈ Quorum : Q1 ∩ Q2 ≠ {}  

THEOREM QuorumNonEmpty ≜ ∀ Q ∈ Quorum : Q ≠ {}
-----------------------------------------------------------------------------
(***************************************************************************)
(* Ballot is a set of "ballot numbers".  For simplicity, we let it be the  *)
(* set of natural numbers.  However, we write Ballot for that set to       *)
(* distinguish ballots from natural numbers used for other purposes.       *)
(***************************************************************************)
Ballot ≜ ℕ
-----------------------------------------------------------------------------
(***************************************************************************)
(* In the algorithm, each acceptor can cast one or more votes, where each  *)
(* vote cast by an acceptor has the form <<b, v>> indicating that the      *)
(* acceptor has voted for value v in ballot b.  A value is chosen if a     *)
(* quorum of acceptors have voted for it in the same ballot.               *)
(***************************************************************************)


(***************************************************************************)
(* The algorithm's variables.                                              *)
(***************************************************************************)
VARIABLE votes,   \* votes[a] is the set of votes cast by acceptor a
         maxBal   \* maxBal[a] is a ballot number.  Acceptor a will cast
                  \*   further votes only in ballots numbered \geq maxBal[a]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK ≜ ∧ votes ∈ [Acceptor → SUBSET (Ballot × Value)]
         ∧ maxBal ∈ [Acceptor → Ballot ∪ {-1}]
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now make a series of definitions an assert some simple theorems      *)
(* about those definitions that lead to the algorithm.                     *)
(***************************************************************************)
VotedFor(a, b, v) ≜ ⟨b, v⟩ ∈ votes[a]
  (*************************************************************************)
  (* True iff acceptor a has voted for v in ballot b.                      *)
  (*************************************************************************)
  
ChosenAt(b, v) ≜ ∃ Q ∈ Quorum : 
                     ∀ a ∈ Q : VotedFor(a, b, v)
  (*************************************************************************)
  (* True iff a quorum of acceptors have all voted for v in ballot b.      *)
  (*************************************************************************)

chosen ≜ {v ∈ Value : ∃ b ∈ Ballot : ChosenAt(b, v)}
  (*************************************************************************)
  (* The set of values that have been chosen.                              *)
  (*************************************************************************)
  
DidNotVoteAt(a, b) ≜ ∀ v ∈ Value : ¬ VotedFor(a, b, v) 

CannotVoteAt(a, b) ≜ ∧ maxBal[a] > b
                     ∧ DidNotVoteAt(a, b)
  (*************************************************************************)
  (* Because acceptor a will not cast any more votes in a ballot numbered  *)
  (* < maxBal[a], this implies that a has not and will never cast a vote   *)
  (* in ballot b.                                                          *)
  (*************************************************************************)

NoneOtherChoosableAt(b, v) ≜ 
   ∃ Q ∈ Quorum :
     ∀ a ∈ Q : VotedFor(a, b, v) ∨ CannotVoteAt(a, b)
  (*************************************************************************)
  (* If this is true, then ChosenAt(b, w) is not and can never become true *)
  (* for any w # v.                                                        *)
  (*************************************************************************)

SafeAt(b, v) ≜ ∀ c ∈ 0‥(b-1) : NoneOtherChoosableAt(c, v)
  (*************************************************************************)
  (* If this is true, then no value other than v has been or can ever be   *)
  (* chosen in any ballot numbered less than b.                            *)
  (*************************************************************************)
-----------------------------------------------------------------------------
THEOREM AllSafeAtZero ≜ ∀ v ∈ Value : SafeAt(0, v)
-----------------------------------------------------------------------------
THEOREM ChoosableThm ≜
          ∀ b ∈ Ballot, v ∈ Value : 
             ChosenAt(b, v) ⇒ NoneOtherChoosableAt(b, v)
-----------------------------------------------------------------------------
VotesSafe ≜ ∀ a ∈ Acceptor, b ∈ Ballot, v ∈ Value :
                 VotedFor(a, b, v) ⇒ SafeAt(b, v)

OneVote ≜ ∀ a ∈ Acceptor, b ∈ Ballot, v, w ∈ Value : 
              VotedFor(a, b, v) ∧ VotedFor(a, b, w) ⇒ (v = w)
OneValuePerBallot ≜  
    ∀ a1, a2 ∈ Acceptor, b ∈ Ballot, v1, v2 ∈ Value : 
       VotedFor(a1, b, v1) ∧ VotedFor(a2, b, v2) ⇒ (v1 = v2)
-----------------------------------------------------------------------------
THEOREM OneValuePerBallot ⇒ OneVote
-----------------------------------------------------------------------------
THEOREM VotesSafeImpliesConsistency ≜
          ∧ TypeOK 
          ∧ VotesSafe
          ∧ OneVote
          ⇒ ∨ chosen = {}
            ∨ ∃ v ∈ Value : chosen = {v}
-----------------------------------------------------------------------------
ShowsSafeAt(Q, b, v) ≜ 
  ∧ ∀ a ∈ Q : maxBal[a] ≥ b
  ∧ ∃ c ∈ -1‥(b-1) : 
      ∧ (c ≠ -1) ⇒ ∃ a ∈ Q : VotedFor(a, c, v)
      ∧ ∀ d ∈ (c+1)‥(b-1), a ∈ Q : DidNotVoteAt(a, d)
-----------------------------------------------------------------------------
THEOREM ShowsSafety ≜ 
          TypeOK ∧ VotesSafe ∧ OneValuePerBallot ⇒
             ∀ Q ∈ Quorum, b ∈ Ballot, v ∈ Value :
               ShowsSafeAt(Q, b, v) ⇒ SafeAt(b, v)
 
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now write the specification.  The initial condition is               *)
(* straightforward.                                                        *)
(***************************************************************************)
Init ≜ ∧ votes = [a ∈ Acceptor ↦ {}]
       ∧ maxBal = [a ∈ Acceptor ↦ -1]


(***************************************************************************)
(* Next are the actions that make up the next-state action.                *)
(*                                                                         *)
(* An acceptor a is allowed to increase maxBal[a] to a ballot number b at  *)
(* any time.                                                               *)
(***************************************************************************)
IncreaseMaxBal(a, b) ≜
  ∧ b > maxBal[a]
  ∧ maxBal' = [maxBal EXCEPT ![a] = b]
  ∧ UNCHANGED votes

(***************************************************************************)
(* Next is the action in which acceptor a votes for v in ballot b.  The    *)
(* first four conjuncts re enabling conditions.  The first maintains the   *)
(* requirement that the acceptor cannot cast a vote in a ballot less than  *)
(* maxBal[a].  The next two conjuncts maintain the invariance of           *)
(* OneValuePerBallot.  The fourth conjunct maintains the invariance of     *)
(* VotesSafe.                                                              *)
(***************************************************************************)
VoteFor(a, b, v) ≜
    ∧ maxBal[a] ≤ b
    ∧ ∀ vt ∈ votes[a] : vt[1] ≠ b
    ∧ ∀ c ∈ Acceptor \ {a} : 
         ∀ vt ∈ votes[c] : (vt[1] = b) ⇒ (vt[2] = v)
    ∧ ∃ Q ∈ Quorum : ShowsSafeAt(Q, b, v)
    ∧ votes' = [votes EXCEPT ![a] = @ ∪ {⟨b, v⟩}]
    ∧ maxBal' = [maxBal EXCEPT ![a] = b]


(***************************************************************************)
(* The next-state action and the invariant.                                *)
(***************************************************************************)
Next  ≜  ∃ a ∈ Acceptor, b ∈ Ballot : 
            ∨ IncreaseMaxBal(a, b)
            ∨ ∃ v ∈ Value : VoteFor(a, b, v)

Spec ≜ Init ∧ □[Next]_⟨votes, maxBal⟩

Inv ≜ TypeOK ∧ VotesSafe ∧ OneValuePerBallot
-----------------------------------------------------------------------------
THEOREM Invariance ≜ Spec ⇒ □Inv
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following statement instantiates module Consensus with the constant *)
(* Value of this module substituted for the constant Value of module       *)
(* Consensus, and the state function `chosen' defined in this module       *)
(* substituted for the variable `chosen' of module Value.  More precisely, *)
(* for each defined identifier id of module Value, this statement defines  *)
(* C!id to equal the value of id under these substitutions.                *)
(***************************************************************************)
C ≜ INSTANCE Consensus

THEOREM Spec ⇒ C!Spec 
<1>1. Inv ∧ Init ⇒ C!Init
<1>2. Inv ∧ [Next]_⟨votes, maxBal⟩ ⇒ [C!Next]_chosen
<1>3. QED
  BY <1>1, <1>2, Invariance, PTL DEF Spec, C!Spec

=============================================================================
