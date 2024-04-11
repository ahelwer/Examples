--------------------------- MODULE FastPaxos -----------------------------
(*
    This is a simplified specification of Leslie Lamport's Fast Paxos protocol.
    The following papers, Fast Paxos by Leslie Lamport and Fast Paxos Made Easy: Theory and Implementation by Zhao Wenbing
    was referenced in writing this specification.

    This simplified specification was written by Lim Ngian Xin Terry & Gaurav Gandhi.

    The following assumptions are made in this simplified specification.

    1. There is a unique coordinator in the system. Therefore, Phase 1a and 1b can be omitted.

    2. All agents in the system can communicate with one another.

    3. Agents must have some stable storage that survives failure and restarts.
       An agent restores its state from stable storage when it restarts, so the failure of an agent
       is indistinguishable from its simply pausing. There is thus no need to model failures explicitly.
*)

EXTENDS Paxos

CONSTANTS FastQuorums, FastBallots

VARIABLES cValue \* Value chosen by coordinator.

ClassicBallots ≜ Ballots \ FastBallots \* The set of ballots of classic rounds.

FastAssume ≜
    ∧ ∀ q ∈ FastQuorums : q ⊆ Replicas
    ∧ ∀ q, r ∈ FastQuorums : q ∩ r ≠ {}
    ∧ ∀ q ∈ FastQuorums : (3 * Cardinality(Replicas)) ÷ 4 ≤ Cardinality(q)
    ∧ ∀ q ∈ Quorums : ∀ r, s ∈ FastQuorums : q ∩ r ∩ s ≠ {}

ASSUME PaxosAssume ∧ FastAssume

IsMajorityValue(M, v) ≜ Cardinality(M) ÷ 2 < Cardinality({m ∈ M : m.value = v})

(*
    Phase 2a (Fast):

    The coordinator starts a fast round by sending a P2a "Any" message, if no other values has been proposed before.
*)
FastAny ≜
    ∧ UNCHANGED⟨decision, maxBallot, maxVBallot, maxValue, cValue⟩
    ∧ ∃ f ∈ FastBallots :
        ∧ SendMessage([type ↦ "P2a",
                        ballot ↦ f,
                        value ↦ any])

(*
    Phase 2b (Fast):

    Acceptors can reply to a P2a "Any" message with a P2b message containing their proposed value.
*)
FastPropose ≜
    ∧ UNCHANGED⟨decision, cValue⟩
    ∧ ∃ a ∈ Replicas, m ∈ p2aMessages, v ∈ Values:
        ∧ m.value = any
        ∧ maxBallot[a] ≤ m.ballot
        ∧ maxValue[a] = none ∨ maxValue[a] = v
        ∧ maxBallot' = [maxBallot EXCEPT ![a] = m.ballot]
        ∧ maxVBallot' = [maxVBallot EXCEPT ![a] = m.ballot]
        ∧ maxValue' = [maxValue EXCEPT ![a] = v]
        ∧ ∀ n ∈ p2bMessages : ¬(n.ballot = m.ballot ∧ n.acceptor = a)
        ∧ SendMessage([type ↦ "P2b",
                        ballot ↦ m.ballot,
                        acceptor ↦ a,
                        value ↦ v])

(*
    A value is chosen if a fast quorum of acceptors proposed that value in a fast round.

    Because the quorum size of a fast round and classic round is different, we assume that the acceptor distinguishes
    a fast round and classic round based on the P2a message it receives. If the P2a message contains the special value
    "any", it is a fast round. Else it is a classic round.
*)
FastDecide ≜
    ∧ UNCHANGED⟨messages, maxBallot, maxVBallot, maxValue, cValue⟩
    ∧ ∃ b ∈ FastBallots, q ∈ FastQuorums :
        LET M ≜ {m ∈ p2bMessages : m.ballot = b ∧ m.acceptor ∈ q}
            V ≜ {w ∈ Values : ∃ m ∈ M : w = m.value}
        IN ∧ ∀ a ∈ q : ∃ m ∈ M : m.acceptor = a
           ∧ 1 = Cardinality(V)
           ∧ ∃ m ∈ M : decision' = m.value

(*
    Phase 2a (Classic)

    If more than one value has been proposed, the collision is resolved using the following rules:

    1. If the proposals contain different values, a value must be selected if the majority of
       acceptors in the fast quorum have casted a vote for that value.

    2. Otherwise, the coordinator is free to select any value.
*)
ClassicAccept ≜
    ∧ UNCHANGED⟨decision, maxBallot, maxVBallot, maxValue⟩
    ∧ ∃ b ∈ ClassicBallots, f ∈ FastBallots, q ∈ FastQuorums, v ∈ Values :
        ∧ f < b \* There was a fast round before this classic round.
        ∧ cValue = none ∨ cValue = v
        ∧ cValue' = v
        ∧ ∀ m ∈ p2aMessages : m.ballot ≠ b
        ∧ LET M ≜ {m ∈ p2bMessages : m.ballot = f ∧ m.acceptor ∈ q}
               V ≜ {w ∈ Values : ∃ m ∈ M : w = m.value}
           IN ∧ ∀ a ∈ q : ∃ m ∈ M : m.acceptor = a
              ∧ 1 < Cardinality(V) \* Collision occurred.
              ∧ IF ∃ w ∈ V : IsMajorityValue(M, w)
                 THEN IsMajorityValue(M, v) \* Choose majority in quorum.
                 ELSE v ∈ V \* Choose any.
              ∧ SendMessage([type ↦ "P2a",
                              ballot ↦ b,
                              value ↦ v])

(*
    Phase 2b (Classic)

    Same as in Paxos.
*)
ClassicAccepted ≜
    ∧ UNCHANGED⟨cValue⟩
    ∧ PaxosAccepted

(*
    Consensus is achieved when a majority of acceptors accept the same ballot number.

    Functionally similar to PaxosDecide in Paxos.tla, but we also have to
    ensure that it can only occur in classic rounds and not fast rounds.
*)
ClassicDecide ≜
    ∧ UNCHANGED⟨messages, maxBallot, maxVBallot, maxValue, cValue⟩
    ∧ ∃ b ∈ ClassicBallots, q ∈ Quorums :
        LET M ≜ {m ∈ p2bMessages : m.ballot = b ∧ m.acceptor ∈ q}
        IN ∧ ∀ a ∈ q : ∃ m ∈ M : m.acceptor = a
           ∧ ∃ m ∈ M : decision' = m.value

FastTypeOK ≜ ∧ PaxosTypeOK
             ∧ cValue ∈ Values ∪ {none}

FastInit ≜ ∧ PaxosInit
           ∧ cValue = none

FastNext ≜ ∨ FastAny
           ∨ FastPropose
           ∨ FastDecide
           ∨ ClassicAccept
           ∨ ClassicAccepted
           ∨ ClassicDecide

FastSpec ≜ ∧ FastInit
           ∧ □[FastNext]_⟨messages, decision, maxBallot, maxVBallot, maxValue, cValue⟩
           ∧ SF_⟨messages, decision, maxBallot, maxVBallot, maxValue, cValue⟩(FastDecide)
           ∧ SF_⟨messages, decision, maxBallot, maxVBallot, maxValue, cValue⟩(ClassicDecide)

\* Non-triviality safety property: Only proposed values can be learnt.
FastNontriviality ≜ ∨ decision = none
                    ∨ ∃ m ∈ p2bMessages : m.value = decision ∧ m.ballot ∈ FastBallots

===============================================================