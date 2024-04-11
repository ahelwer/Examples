---------------------------- MODULE BPConProof ------------------------------
(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

----------------------------------------------------------------------------
(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PConProof specs.                                                        *)
(***************************************************************************)
CONSTANT Value

Ballot ≜ ℕ

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
None ≜ CHOOSE v : v ∉ Value
-----------------------------------------------------------------------------
(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the PCon algorithm.                                                     *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including acting like a good one.   *)
(*                                                                         *)
(* The basic idea is that the good acceptors try to execute the Paxos      *)
(* consensus algorithm, while the bad acceptors may try to prevent them.   *)
(*                                                                         *)
(* We do not distinguish between faulty and non-faulty leaders.  Safety    *)
(* must be preserved even if all leaders are malicious, so we allow any    *)
(* leader to send any syntactically correct message at any time.  (In an   *)
(* implementation, syntactically incorrect messages are simply ignored by  *)
(* non-faulty acceptors and have no effect.) Assumptions about leader      *)
(* behavior are required only for liveness.                                *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
          WeakQuorum
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)
ByzAcceptor ≜ Acceptor ∪ FakeAcceptor

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)
ASSUME BallotAssump ≜ (Ballot ∪ {-1}) ∩ ByzAcceptor = {}

(***************************************************************************)
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)
ASSUME BQA ≜
          ∧ Acceptor ∩ FakeAcceptor = {}
          ∧ ∀ Q ∈ ByzQuorum : Q ⊆ ByzAcceptor
          ∧ ∀ Q1, Q2 ∈ ByzQuorum : Q1 ∩ Q2 ∩ Acceptor ≠ {}
          ∧ ∀ Q ∈ WeakQuorum : ∧ Q ⊆ ByzAcceptor
                               ∧ Q ∩ Acceptor ≠ {}

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
ASSUME BQLA ≜
          ∧ ∃ Q ∈ ByzQuorum : Q ⊆ Acceptor
          ∧ ∃ Q ∈ WeakQuorum : Q ⊆ Acceptor
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage ≜ [type : {"1a"},  bal : Ballot]
  (*************************************************************************)
  (* Type 1a messages are the same as in module PConProof.                 *)
  (*************************************************************************)

1bMessage ≜
  (*************************************************************************)
  (* A 1b message serves the same function as a 1b message in ordinary     *)
  (* Paxos, where the mbal and mval components correspond to the mbal and  *)
  (* mval components in the 1b messages of PConProof.  The m2av component  *)
  (* is set containing all records with val and bal components equal to    *)
  (* the corresponding of components of a 2av message that the acceptor    *)
  (* has sent, except containing for each val only the record              *)
  (* corresponding to the 2av message with the highest bal component.      *)
  (*************************************************************************)
  [type : {"1b"}, bal : Ballot,
   mbal : Ballot ∪ {-1}, mval : Value ∪ {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage ≜
  (*************************************************************************)
  (* Type 1c messages are the same as in PConProof.                        *)
  (*************************************************************************)
  [type : {"1c"}, bal : Ballot, val : Value]

2avMessage ≜
  (*************************************************************************)
  (* When an acceptor receives a 1c message, it relays that message's      *)
  (* contents to the other acceptors in a 2av message.  It does this only  *)
  (* for the first 1c message it receives for that ballot; it can receive  *)
  (* a second 1c message only if the leader is malicious, in which case it *)
  (* ignores that second 1c message.                                       *)
  (*************************************************************************)
   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage ≜ [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]
  (*************************************************************************)
  (* 2b messages are the same as in ordinary Paxos.                        *)
  (*************************************************************************)

BMessage ≜
  1aMessage ∪ 1bMessage ∪ 1cMessage ∪ 2avMessage ∪ 2bMessage

(***************************************************************************)
(* We will need the following simple fact about these sets of messages.    *)
(***************************************************************************)
LEMMA BMessageLemma ≜
         ∀ m ∈ BMessage :
           ∧ (m ∈ 1aMessage) ⇔  (m.type = "1a")
           ∧ (m ∈ 1bMessage) ⇔  (m.type = "1b")
           ∧ (m ∈ 1cMessage) ⇔  (m.type = "1c")
           ∧ (m ∈ 2avMessage) ⇔  (m.type = "2av")
           ∧ (m ∈ 2bMessage) ⇔  (m.type = "2b")
<1>1. ∧ ∀ m ∈ 1aMessage : m.type = "1a"
      ∧ ∀ m ∈ 1bMessage : m.type = "1b"
      ∧ ∀ m ∈ 1cMessage : m.type = "1c"
      ∧ ∀ m ∈ 2avMessage : m.type = "2av"
      ∧ ∀ m ∈ 2bMessage : m.type = "2b"
  BY DEF 1aMessage, 1bMessage, 1cMessage, 2avMessage, 2bMessage
<1>2. QED
  BY <1>1 DEF BMessage
-----------------------------------------------------------------------------


(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PCon algorithm with
Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PCon algorithm or if it
is malicious.

The main idea of the algorithm is that, before performing an action of
the PCon algorithm, a good acceptor determines that this action is
actually enabled in that algorithm.  Since an action is enabled by the
receipt of one or more messages, the acceptor has to determine that
the enabling messages are legal PCon messages.  Because algorithm PCon
allows a 1a message to be sent at any time, the only acceptor action
whose enabling messages must be checked is the Phase2b action.  It is
enabled iff the appropriate 1c message and 2a message are legal.  The
1c message is legal iff the leader has received the necessary 1b
messages.  The acceptor therefore maintains a set of 1b messages that
it knows have been sent, and checks that those 1b messages enable the
sending of the 1c message.

A 2a message is legal in the PCon algorithm iff (i) the corresponding
1c message is legal and (ii) it is the only 2a message that the leader
sends.  In the BPCon algorithm, there are no explicit 2a messages.
They are implicitly sent by the acceptors when they send enough 2av
messages.

We leave unspecified how an acceptor discovers what 1b messages have
been sent.  In the Castro-Liskov algorithm, this is done by having
acceptors relay messages sent by other acceptors.  An acceptor knows
that a 1b message has been sent if it receives it directly or else
receives a copy from a weak Byzantine quorum of acceptors.  A
(non-malicious) leader must determine what 1b messages acceptors know
about so it chooses a value so that a quorum of acceptors will act on
its Phase1c message and cause that value to be chosen.  However, this
is necessary only for liveness, so we ignore this for now.

In other implementations of our algorithm, the leader sends along with
the 1c message a proof that the necessary 1b messages have been sent.
The easiest way to do this is to have acceptors digitally sign their 1b
messages, so a copy of the message proves that it has been sent (by the
acceptor indicated in the message's acc field).  The necessary proofs
can also be constructed using only message authenticators (like the
ones used in the Castro-Liskov algorithm); how this is done is
described elsewhere.

In the abstract algorithm presented here, which we call
BPCon, we do not specify how acceptors learn what 1b
messages have been sent.  We simply introduce a variable knowsSent such
that knowsSent[a] represents the set of 1b messages that (good)
acceptor a knows have been sent, and have an action that
nondeterministically adds sent 1b messages to this set.

--algorithm BPCon {
  (**************************************************************************
The variables:

    maxBal[a]  = Highest ballot in which acceptor a has participated.

    maxVBal[a] = Highest ballot in which acceptor a has cast a vote
                 (sent a 2b message); or -1 if it hasn't cast a vote.

    maxVVal[a] = Value acceptor a has voted for in ballot maxVBal[a],
                  or None if maxVBal[a] = -1.

    2avSent[a] = A set of records in [val : Value, bal : Ballot]
                 describing the 2av messages that a has sent.  A
                 record is added to this set, and any element with
                 the same val field (and lower bal field) removed
                 when a sends a 2av message.

    knownSent[a] = The set of 1b messages that acceptor a knows have
                   been sent.

    bmsgs = The set of all messages that have been sent.  See the
            discussion of the msgs variable in module PConProof
            to understand our modeling of message passing.
  **************************************************************************)
  variables maxBal  = [a ∈ Acceptor ↦ -1],
            maxVBal = [a ∈ Acceptor ↦ -1] ,
            maxVVal = [a ∈ Acceptor ↦ None] ,
            2avSent = [a ∈ Acceptor ↦ {}],
            knowsSent = [a ∈ Acceptor ↦ {}],
            bmsgs = {}
  define {
    sentMsgs(type, bal) ≜ {m ∈ bmsgs: m.type = type ∧ m.bal = bal}

    KnowsSafeAt(ac, b, v) ≜
      (*********************************************************************)
      (* True for an acceptor ac, ballot b, and value v iff the set of 1b  *)
      (* messages in knowsSent[ac] implies that value v is safe at ballot  *)
      (* b in the PaxosConsensus algorithm being emulated by the good      *)
      (* acceptors.  To understand the definition, see the definition of   *)
      (* ShowsSafeAt in module PConProof and recall (a) the meaning of the *)
      (* mCBal and mCVal fields of a 1b message and (b) that the set of    *)
      (* real acceptors in a ByzQuorum forms a quorum of the               *)
      (* PaxosConsensus algorithm.                                         *)
      (*********************************************************************)
      LET S ≜ {m ∈ knowsSent[ac] : m.bal = b}
      IN  ∨ ∃ BQ ∈ ByzQuorum :
               ∀ a ∈ BQ : ∃ m ∈ S : ∧ m.acc = a
                                    ∧ m.mbal = -1
          ∨ ∃ c ∈ 0‥(b-1):
               ∧ ∃ BQ ∈ ByzQuorum :
                    ∀ a ∈ BQ : ∃ m ∈ S : ∧ m.acc = a
                                         ∧ m.mbal ≤ c
                                         ∧ (m.mbal = c) ⇒ (m.mval = v)
               ∧ ∃ WQ ∈ WeakQuorum :
                    ∀ a ∈ WQ :
                      ∃ m ∈ S : ∧ m.acc = a
                                ∧ ∃ r ∈ m.m2av : ∧ r.bal ≥ c
                                                 ∧ r.val = v
   }

  (*************************************************************************)
  (* We now describe the processes' actions as macros.                     *)
  (*                                                                       *)
  (* The following two macros send a message and a set of messages,        *)
  (* respectively.  These macros are so simple that they're hardly worth   *)
  (* introducing, but they do make the processes a little easier to read.  *)
  (*************************************************************************)
  macro SendMessage(m) { bmsgs ≔ bmsgs ∪ {m} }
  macro SendSetOfMessages(S) { bmsgs ≔ bmsgs ∪ S }

  (*************************************************************************)
  (* As in the Paxos consensus algorithm, a ballot `self' leader (good or  *)
  (* malicious) can execute a Phase1a ation at any time.                   *)
  (*************************************************************************)
  macro Phase1a() { SendMessage([type ↦ "1a", bal ↦ self]) }

  (*************************************************************************)
  (* The acceptor's Phase1b ation is similar to that of the PaxosConsensus *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  macro Phase1b(b) {
   when (b > maxBal[self]) ∧ (sentMsgs("1a", b) ≠ {}) ;
   maxBal[self] ≔ b ;
   SendMessage([type ↦ "1b", bal ↦ b, acc ↦ self, m2av ↦ 2avSent[self],
                mbal ↦ maxVBal[self], mval ↦ maxVVal[self]])
   }

  (*************************************************************************)
  (* A good ballot `self' leader can send a phase 1c message for value v   *)
  (* if it knows that the messages in knowsSent[a] for a Quorum of (good)  *)
  (* acceptors imply that they know that v is safe at ballot `self', and   *)
  (* that they can convince any other acceptor that the appropriate 1b     *)
  (* messages have been sent to that it will also know that v is safe at   *)
  (* ballot `self'.                                                        *)
  (*                                                                       *)
  (* A malicious ballot `self' leader can send any phase 1c messages it    *)
  (* wants (including one that a good leader could send).  We prove safety *)
  (* with a Phase1c ation that allows a leader to be malicious.  To prove  *)
  (* liveness, we will have to assume a good leader that sends only        *)
  (* correct 1c messages.                                                  *)
  (*                                                                       *)
  (* As in the PaxosConsensus algorithm, we allow a Phase1c action to send *)
  (* a set of Phase1c messages.  (This is not done in the Castro-Liskov    *)
  (* algorithm, but seems natural in light of the PaxosConsensus           *)
  (* algorithm.)                                                           *)
  (*************************************************************************)
  macro Phase1c() {
    with (S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]) {
      SendSetOfMessages(S) }
   }

  (*************************************************************************)
  (* If acceptor `self' receives a ballot b phase 1c message with value v, *)
  (* it relays v in a phase 2av message if                                 *)
  (*                                                                       *)
  (*   - it has not already sent a 2av message in this or a later          *)
  (*     ballot and                                                        *)
  (*                                                                       *)
  (*   - the messages in knowsSent[self] show it that v is safe at b in    *)
  (*     the non-Byzantine Paxos consensus algorithm being emulated.       *)
  (*************************************************************************)
  macro Phase2av(b) {
    when ∧ maxBal[self] ≤ b
         ∧ ∀ r ∈ 2avSent[self] : r.bal < b ;
            \* We could just as well have used r.bal # b in this condition.
    with (m ∈ {ms ∈ sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       SendMessage([type ↦ "2av", bal ↦ b, val ↦ m.val, acc ↦ self]) ;
       2avSent[self] ≔  {r ∈ 2avSent[self] : r.val ≠ m.val}
                           ∪ {[val ↦ m.val, bal ↦ b]}
      } ;
    maxBal[self]  ≔ b ;
   }

  (*************************************************************************)
  (* Acceptor `self' can send a phase 2b message with value v if it has    *)
  (* received phase 2av messages from a Byzantine quorum, which implies    *)
  (* that a quorum of good acceptors assert that this is the first 1c      *)
  (* message sent by the leader and that the leader was allowed to send    *)
  (* that message.  It sets maxBal[self], maxVBal[self], and maxVVal[self] *)
  (* as in the non-Byzantine algorithm.                                    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when maxBal[self] ≤ b ;
    with (v ∈ {vv ∈ Value :
                   ∃ Q ∈ ByzQuorum :
                      ∀ aa ∈ Q :
                         ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = vv
                                                    ∧ m.acc = aa} ) {
        SendMessage([type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]) ;
        maxVVal[self] ≔ v ;
      } ;
    maxBal[self] ≔ b ;
    maxVBal[self] ≔ b
   }

  (*************************************************************************)
  (* At any time, an acceptor can learn that some set of 1b messages were  *)
  (* sent (but only if they atually were sent).                            *)
  (*************************************************************************)
  macro LearnsSent(b) {
    with (S ∈ SUBSET sentMsgs("1b", b)) {
       knowsSent[self] ≔ knowsSent[self] ∪ S
     }
   }
  (*************************************************************************)
  (* A malicious acceptor `self' can send any acceptor message indicating  *)
  (* that it is from itself.  Since a malicious acceptor could allow other *)
  (* malicious processes to forge its messages, this action could          *)
  (* represent the sending of the message by any malicious process.        *)
  (*************************************************************************)
  macro FakingAcceptor() {
    with ( m ∈ { mm ∈ 1bMessage ∪ 2avMessage ∪ 2bMessage :
                   mm.acc = self} ) {
         SendMessage(m)
     }
   }

  (*************************************************************************)
  (* We combine these individual actions into a complete algorithm in the  *)
  (* usual way, with separate process declarations for the acceptor,       *)
  (* leader, and fake acceptor processes.                                  *)
  (*************************************************************************)
  process (acceptor ∈ Acceptor) {
    acc: while (TRUE) {
           with (b ∈ Ballot) {either Phase1b(b) or Phase2av(b)
                                  or Phase2b(b) or LearnsSent(b)}
    }
   }

  process (leader ∈ Ballot) {
    ldr: while (TRUE) {
          either Phase1a() or Phase1c()
         }
   }

  process (facceptor ∈ FakeAcceptor) {
     facc : while (TRUE) { FakingAcceptor() }
   }
}

Below is the TLA+ translation, as produced by the translator.  (Some
blank lines have been removed.)
**************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

(* define statement *)
sentMsgs(type, bal) ≜ {m ∈ bmsgs: m.type = type ∧ m.bal = bal}

KnowsSafeAt(ac, b, v) ≜
  LET S ≜ {m ∈ knowsSent[ac] : m.bal = b}
  IN  ∨ ∃ BQ ∈ ByzQuorum :
           ∀ a ∈ BQ : ∃ m ∈ S : ∧ m.acc = a
                                ∧ m.mbal = -1
      ∨ ∃ c ∈ 0‥(b-1):
           ∧ ∃ BQ ∈ ByzQuorum :
                ∀ a ∈ BQ : ∃ m ∈ S : ∧ m.acc = a
                                     ∧ m.mbal ≤ c
                                     ∧ (m.mbal = c) ⇒ (m.mval = v)
           ∧ ∃ WQ ∈ WeakQuorum :
                ∀ a ∈ WQ :
                  ∃ m ∈ S : ∧ m.acc = a
                            ∧ ∃ r ∈ m.m2av : ∧ r.bal ≥ c
                                             ∧ r.val = v


vars ≜ ⟨ maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs ⟩

ProcSet ≜ (Acceptor) ∪ (Ballot) ∪ (FakeAcceptor)

Init ≜ (* Global variables *)
        ∧ maxBal = [a ∈ Acceptor ↦ -1]
        ∧ maxVBal = [a ∈ Acceptor ↦ -1]
        ∧ maxVVal = [a ∈ Acceptor ↦ None]
        ∧ 2avSent = [a ∈ Acceptor ↦ {}]
        ∧ knowsSent = [a ∈ Acceptor ↦ {}]
        ∧ bmsgs = {}

acceptor(self) ≜ ∃ b ∈ Ballot:
                    ∨ ∧ (b > maxBal[self]) ∧ (sentMsgs("1a", b) ≠ {})
                      ∧ maxBal' = [maxBal EXCEPT ![self] = b]
                      ∧ bmsgs' = (bmsgs ∪ {([type ↦ "1b", bal ↦ b, acc ↦ self, m2av ↦ 2avSent[self],
                                                  mbal ↦ maxVBal[self], mval ↦ maxVVal[self]])})
                      ∧ UNCHANGED ⟨maxVBal, maxVVal, 2avSent, knowsSent⟩
                    ∨ ∧ ∧ maxBal[self] ≤ b
                        ∧ ∀ r ∈ 2avSent[self] : r.bal < b
                      ∧ ∃ m ∈ {ms ∈ sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
                            ∧ bmsgs' = (bmsgs ∪ {([type ↦ "2av", bal ↦ b, val ↦ m.val, acc ↦ self])})
                            ∧ 2avSent' = [2avSent EXCEPT ![self] = {r ∈ 2avSent[self] : r.val ≠ m.val}
                                                                      ∪ {[val ↦ m.val, bal ↦ b]}]
                      ∧ maxBal' = [maxBal EXCEPT ![self] = b]
                      ∧ UNCHANGED ⟨maxVBal, maxVVal, knowsSent⟩
                    ∨ ∧ maxBal[self] ≤ b
                      ∧ ∃ v ∈ {vv ∈ Value :
                                      ∃ Q ∈ ByzQuorum :
                                         ∀ aa ∈ Q :
                                            ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = vv
                                                                       ∧ m.acc = aa}:
                            ∧ bmsgs' = (bmsgs ∪ {([type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v])})
                            ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
                      ∧ maxBal' = [maxBal EXCEPT ![self] = b]
                      ∧ maxVBal' = [maxVBal EXCEPT ![self] = b]
                      ∧ UNCHANGED ⟨2avSent, knowsSent⟩
                    ∨ ∧ ∃ S ∈ SUBSET sentMsgs("1b", b):
                            knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] ∪ S]
                      ∧ UNCHANGED ⟨maxBal, maxVBal, maxVVal, 2avSent, bmsgs⟩


leader(self) ≜ ∧ ∨ ∧ bmsgs' = (bmsgs ∪ {([type ↦ "1a", bal ↦ self])})
                 ∨ ∧ ∃ S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                           bmsgs' = (bmsgs ∪ S)
               ∧ UNCHANGED ⟨ maxBal, maxVBal, maxVVal, 2avSent, knowsSent ⟩


facceptor(self) ≜ ∧ ∃ m ∈ { mm ∈ 1bMessage ∪ 2avMessage ∪ 2bMessage :
                                 mm.acc = self}:
                        bmsgs' = (bmsgs ∪ {m})
                  ∧ UNCHANGED ⟨ maxBal, maxVBal, maxVVal, 2avSent,
                                   knowsSent ⟩


Next ≜ (∃ self ∈ Acceptor: acceptor(self))
           ∨ (∃ self ∈ Ballot: leader(self))
           ∨ (∃ self ∈ FakeAcceptor: facceptor(self))

Spec ≜ Init ∧ □[Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* As in module PConProof, we now rewrite the next-state relation in a     *)
(* form more convenient for writing proofs.                                *)
(***************************************************************************)
Phase1b(self, b) ≜
  ∧ (b > maxBal[self]) ∧ (sentMsgs("1a", b) ≠ {})
  ∧ maxBal' = [maxBal EXCEPT ![self] = b]
  ∧ bmsgs' = bmsgs ∪ {[type  ↦ "1b", bal ↦ b, acc ↦ self,
                           m2av ↦ 2avSent[self],
                           mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]}
  ∧ UNCHANGED ⟨maxVBal, maxVVal, 2avSent, knowsSent⟩

Phase2av(self, b) ≜
  ∧ maxBal[self] ≤ b
  ∧ ∀ r ∈ 2avSent[self] : r.bal < b
  ∧ ∃ m ∈ {ms ∈ sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       ∧ bmsgs' = bmsgs ∪
                    {[type ↦ "2av", bal ↦ b, val ↦ m.val, acc ↦ self]}
       ∧ 2avSent' = [2avSent EXCEPT
                        ![self] = {r ∈ 2avSent[self] : r.val ≠ m.val}
                                    ∪ {[val ↦ m.val, bal ↦ b]}]
  ∧ maxBal' = [maxBal EXCEPT ![self] = b]
  ∧ UNCHANGED ⟨maxVBal, maxVVal, knowsSent⟩

Phase2b(self, b) ≜
  ∧ maxBal[self] ≤ b
  ∧ ∃ v ∈ {vv ∈ Value :
                 ∃ Q ∈ ByzQuorum :
                    ∀ a ∈ Q :
                       ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = vv
                                                  ∧ m.acc = a }:
       ∧ bmsgs' = (bmsgs ∪
                     {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]})
       ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
  ∧ maxBal' = [maxBal EXCEPT ![self] = b]
  ∧ maxVBal' = [maxVBal EXCEPT ![self] = b]
  ∧ UNCHANGED ⟨2avSent, knowsSent⟩

LearnsSent(self, b) ≜
 ∧ ∃ S ∈ SUBSET sentMsgs("1b", b):
       knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] ∪ S]
 ∧ UNCHANGED ⟨maxBal, maxVBal, maxVVal, 2avSent, bmsgs⟩

Phase1a(self) ≜
  ∧ bmsgs' = (bmsgs ∪ {[type ↦ "1a", bal ↦ self]})
  ∧ UNCHANGED ⟨ maxBal, maxVBal, maxVVal, 2avSent, knowsSent ⟩

Phase1c(self) ≜
  ∧ ∃ S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                        bmsgs' = (bmsgs ∪ S)
  ∧ UNCHANGED ⟨ maxBal, maxVBal, maxVVal, 2avSent, knowsSent ⟩

FakingAcceptor(self) ≜
  ∧ ∃ m ∈ { mm ∈ 1bMessage ∪ 2avMessage ∪ 2bMessage : mm.acc = self} :
         bmsgs' = (bmsgs ∪ {m})
  ∧ UNCHANGED ⟨ maxBal, maxVBal, maxVVal, 2avSent, knowsSent ⟩
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma describes how the next-state relation Next can be   *)
(* written in terms of the actions defined above.                          *)
(***************************************************************************)
LEMMA NextDef ≜
 Next ⇔ ∨ ∃ self ∈ Acceptor :
                ∃ b ∈ Ballot : ∨ Phase1b(self, b)
                               ∨ Phase2av(self, b)
                               ∨ Phase2b(self,b)
                               ∨ LearnsSent(self, b)
        ∨ ∃ self ∈ Ballot : ∨ Phase1a(self)
                            ∨ Phase1c(self)
        ∨ ∃ self ∈ FakeAcceptor : FakingAcceptor(self)
<1>1. ∀ self : acceptor(self) ⇔ NextDef!2!1!(self)
  BY  DEF acceptor, Phase1b,  Phase2av, Phase2b, LearnsSent
<1>2. ∀ self : leader(self) ⇔ NextDef!2!2!(self)
  BY DEF leader, Phase1a, Phase1c
<1>3. ∀ self : facceptor(self) ⇔ NextDef!2!3!(self)
  BY DEF facceptor, FakingAcceptor
<1>4. QED
      BY <1>1, <1>2, <1>3, Zenon
      DEF Next, acceptor, leader, facceptor
-----------------------------------------------------------------------------
(***************************************************************************)
(*                        THE REFINEMENT MAPPING                           *)
(***************************************************************************)

(***************************************************************************)
(* We define a quorum to be the set of acceptors in a Byzantine quorum.    *)
(* The quorum assumption QA of module PConProof, which we here call        *)
(* QuorumTheorem, follows easily from the definition and assumption BQA.   *)
(***************************************************************************)
Quorum ≜ {S ∩ Acceptor : S ∈ ByzQuorum}

THEOREM QuorumTheorem ≜
         ∧ ∀ Q1, Q2 ∈ Quorum : Q1 ∩ Q2 ≠ {}
         ∧ ∀ Q ∈ Quorum : Q ⊆ Acceptor
BY BQA DEF Quorum

(***************************************************************************)
(* We now define refinement mapping under which our algorithm implements   *)
(* the algorithm of module PConProof.  First, we define the set msgs that  *)
(* implements the variable of the same name in PConProof.  There are two   *)
(* non-obvious parts of the definition.                                    *)
(*                                                                         *)
(* 1.  The 1c messages in msgs should just be the ones that are            *)
(* legal--that is, messages whose value is safe at the indicated ballot.   *)
(* The obvious way to define legality is in terms of 1b messages that have *)
(* been sent.  However, this has the effect that sending a 1b message can  *)
(* add both that 1b message and one or more 1c messages to msgs.  Proving  *)
(* implementation under this refinement mapping would require adding a     *)
(* stuttering variable.  Instead, we define the 1c message to be legal if  *)
(* the set of 1b messages that some acceptor knows were sent confirms its  *)
(* legality.  Thus, those 1c messages are added to msgs by the LearnsSent  *)
(* ation, which has no other effect on the refinement mapping.             *)
(*                                                                         *)
(* 2.  A 2a message is added to msgs when a quorum of acceptors have       *)
(* reacted to it by sending a 2av message.                                 *)
(***************************************************************************)
msgsOfType(t) ≜ {m ∈ bmsgs : m.type = t }

acceptorMsgsOfType(t) ≜ {m ∈ msgsOfType(t) : m.acc ∈  Acceptor}

1bRestrict(m) ≜ [type ↦ "1b", acc ↦ m.acc, bal ↦ m.bal,
                  mbal ↦ m.mbal, mval ↦ m.mval]

1bmsgs ≜ { 1bRestrict(m) : m ∈ acceptorMsgsOfType("1b") }

1cmsgs ≜ {m ∈ msgsOfType("1c") :
                   ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)}

2amsgs ≜ {m ∈ [type : {"2a"}, bal : Ballot, val : Value] :
             ∃ Q ∈ Quorum :
               ∀ a ∈ Q :
                 ∃ m2av ∈ acceptorMsgsOfType("2av") :
                    ∧ m2av.acc = a
                    ∧ m2av.bal = m.bal
                    ∧ m2av.val = m.val }

msgs ≜ msgsOfType("1a") ∪ 1bmsgs ∪ 1cmsgs ∪ 2amsgs
         ∪ acceptorMsgsOfType("2b")

(***************************************************************************)
(* We now define PmaxBal, the state function with which we instantiate the *)
(* variable maxBal of PConProof.  The reason we don't just instantiate it  *)
(* with the variable maxBal is that maxBal[a] can change when acceptor `a' *)
(* performs a Phase2av ation, which does not correspond to any acceptor    *)
(* action of the PCon algorithm.  We want PmaxBal[a] to change only        *)
(* when `a' performs a Phase1b or Phase2b ation--that is, when it sends a  *)
(* 1b or 2b message.  Thus, we define PmaxBal[a] to be the largest bal     *)
(* field of all 1b and 2b messages sent by `a'.                            *)
(*                                                                         *)
(* To define PmaxBal, we need to define an operator MaxBallot so that      *)
(* MaxBallot(S) is the largest element of S if S is non-empty a finite set *)
(* consisting of ballot numbers and possibly the value -1.                 *)
(***************************************************************************)
MaxBallot(S) ≜
  IF S = {} THEN -1
            ELSE CHOOSE mb ∈ S : ∀ x ∈ S : mb  ≥ x

(***************************************************************************)
(* To prove that the CHOOSE in this definition actually does choose a      *)
(* maximum of S when S is nonempty, we need the following fact.            *)
(***************************************************************************)
LEMMA FiniteSetHasMax ≜
        ∀ S ∈ SUBSET ℤ :
          IsFiniteSet(S) ∧ (S ≠ {}) ⇒ ∃ max ∈ S : ∀ x ∈ S : max ≥ x
<1>. DEFINE P(S) ≜ S ⊆ ℤ ∧ S ≠ {} ⇒
                      ∃ max ∈ S : ∀ x ∈ S : max ≥ x
<1>1. P({})
  OBVIOUS
<1>2. ASSUME NEW T, NEW x, P(T)
      PROVE  P(T ∪ {x})
  BY <1>2
<1>3. ∀ S : IsFiniteSet(S) ⇒ P(S)
  <2>. HIDE DEF P
  <2>. QED  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY <1>3, Zenon

(***************************************************************************)
(* Our proofs use this property of MaxBallot.                              *)
(***************************************************************************)
THEOREM MaxBallotProp  ≜
  ASSUME NEW S ∈ SUBSET (Ballot ∪ {-1}),
         IsFiniteSet(S)
  PROVE  IF S = {} THEN MaxBallot(S) = -1
                   ELSE ∧ MaxBallot(S) ∈ S
                        ∧ ∀ x ∈ S : MaxBallot(S) ≥ x
<1>1. CASE S = {}
  BY <1>1 DEF MaxBallot
<1>2. CASE S ≠ {}
  <2>. PICK mb ∈ S : ∀ x ∈ S : mb ≥ x
    BY <1>2,  FiniteSetHasMax DEF Ballot
  <2>. QED  BY <1>2 DEF MaxBallot
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* We now prove a couple of lemmas about MaxBallot.                        *)
(***************************************************************************)
LEMMA MaxBallotLemma1 ≜
        ASSUME NEW S ∈ SUBSET (Ballot ∪ {-1}),
               IsFiniteSet(S),
               NEW y ∈ S, ∀ x ∈ S : y ≥ x
        PROVE  y = MaxBallot(S)
<1>1. ∧ MaxBallot(S) ∈ S
      ∧ MaxBallot(S) ≥ y
  BY MaxBallotProp
<1>2 ∧ y ∈ Ballot ∪ {-1}
     ∧ y ≥ MaxBallot(S)
  BY MaxBallotProp
<1>3. MaxBallot(S) ∈ ℤ ∧ y ∈ ℤ
  BY <1>1, <1>2, Isa DEF Ballot
<1>. QED  BY <1>1, <1>2, <1>3

LEMMA MaxBallotLemma2 ≜
  ASSUME NEW S ∈ SUBSET (Ballot ∪ {-1}),
         NEW T ∈ SUBSET (Ballot ∪ {-1}),
         IsFiniteSet(S), IsFiniteSet(T)
  PROVE  MaxBallot(S ∪ T) = IF MaxBallot(S) ≥ MaxBallot(T)
                               THEN MaxBallot(S) ELSE MaxBallot(T)
<1>1. ∧ MaxBallot(S) ∈ Ballot ∪ {-1}
      ∧ MaxBallot(T) ∈ Ballot ∪ {-1}
  BY MaxBallotProp
<1>. S ∪ T ⊆ ℤ
  BY DEF Ballot
<1>2. CASE MaxBallot(S) ≥ MaxBallot(T)
  <2>. SUFFICES ASSUME T ≠ {}
                PROVE  MaxBallot(S ∪ T) = MaxBallot(S)
    BY <1>2, Zenon
  <2>1. ∧ MaxBallot(T) ∈ T
        ∧ ∀ x ∈ T : MaxBallot(T) ≥ x
    BY MaxBallotProp
  <2>2. CASE S = {}
    <3>1. MaxBallot(S) = -1
      BY <2>2 DEF MaxBallot
    <3>2. MaxBallot(T) = -1
      BY <3>1, <1>2, <1>1 DEF Ballot
    <3>. QED  BY <2>2, <3>1, <3>2, <2>1, MaxBallotLemma1, FS_Union
  <2>3. CASE S ≠ {}
    <3>1. ∧ MaxBallot(S) ∈ S
          ∧ ∀ x ∈ S : MaxBallot(S) ≥ x
      BY <2>3, MaxBallotProp
    <3>2. ∧ MaxBallot(S) ∈ S ∪ T
          ∧ ∀ x ∈ S ∪ T : MaxBallot(S) ≥ x
      BY <3>1, <2>1, <1>2
    <3>. QED  BY <3>2, MaxBallotLemma1, FS_Union, Zenon
  <2>. QED  BY <2>2, <2>3
<1>3. CASE ¬(MaxBallot(S) ≥ MaxBallot(T))
  <2>. SUFFICES ASSUME S ≠ {}
                PROVE  MaxBallot(S ∪ T) = MaxBallot(T)
    BY <1>3
  <2>1. ∧ MaxBallot(S) ∈ S
        ∧ ∀ x ∈ S : MaxBallot(S) ≥ x
    BY MaxBallotProp
  <2>2. ∧ MaxBallot(S) < MaxBallot(T)
        ∧ MaxBallot(T) ≠ -1
    BY <1>3, <1>1 DEF Ballot
  <2>3. ∧ MaxBallot(T) ∈ T
        ∧ ∀ x ∈ T : MaxBallot(T) ≥ x
    BY <2>2, MaxBallotProp
  <2>4. ∧ MaxBallot(T) ∈ S ∪ T
        ∧ ∀ x ∈ S ∪ T : MaxBallot(T) ≥ x
    BY <2>3, <2>2, <2>1
  <2>. QED  BY <2>4, MaxBallotLemma1, FS_Union, Zenon
<1>. QED  BY <1>2, <1>3


(***************************************************************************)
(* We finally come to our definition of PmaxBal, the state function        *)
(* substituted for variable maxBal of module PConProof by our refinement   *)
(* mapping.  We also prove a couple of lemmas about PmaxBal.               *)
(***************************************************************************)

1bOr2bMsgs ≜ {m ∈ bmsgs : m.type ∈ {"1b", "2b"}}

PmaxBal ≜ [a ∈ Acceptor ↦
              MaxBallot({m.bal : m ∈ {ma ∈ 1bOr2bMsgs :
                                           ma.acc = a}})]

LEMMA PmaxBalLemma1 ≜
         ASSUME NEW m ,
                bmsgs' = bmsgs ∪ {m},
                m.type ≠ "1b" ∧ m.type ≠ "2b"
         PROVE  PmaxBal' = PmaxBal
BY Zenon DEF PmaxBal, 1bOr2bMsgs

LEMMA PmaxBalLemma2 ≜
        ASSUME NEW m,
               bmsgs' = bmsgs ∪ {m},
               NEW a ∈ Acceptor,
               m.acc ≠ a
        PROVE  PmaxBal'[a] = PmaxBal[a]
BY DEF PmaxBal, 1bOr2bMsgs

(***************************************************************************)
(* Finally, we define the refinement mapping.  As before, for any operator *)
(* op defined in module PConProof, the following INSTANCE statement        *)
(* defines P!op to be the operator obtained from op by the indicated       *)
(* substitutions, along with the implicit substitutions                    *)
(*                                                                         *)
(*     Acceptor <- Acceptor,                                               *)
(*     Quorum   <- Quorum                                                  *)
(*     Value    <- Value                                                   *)
(*     maxVBal  <- maxVBal                                                 *)
(*     maxVVal  <- maxVVal                                                 *)
(*     msgs     <- msgs                                                    *)
(***************************************************************************)
P ≜ INSTANCE PConProof WITH maxBal ← PmaxBal
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the inductive invariant Inv used in our proof.  It is     *)
(* defined to be the conjunction of a number of separate invariants that   *)
(* we define first, starting with the ever-present type-correctness        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK ≜ ∧ maxBal  ∈ [Acceptor → Ballot ∪ {-1}]
         ∧ 2avSent ∈ [Acceptor → SUBSET [val : Value, bal : Ballot]]
         ∧ maxVBal ∈ [Acceptor → Ballot ∪ {-1}]
         ∧ maxVVal ∈ [Acceptor → Value ∪ {None}]
         ∧ knowsSent ∈ [Acceptor → SUBSET 1bMessage]
         ∧ bmsgs ⊆ BMessage

(***************************************************************************)
(* To use the definition of PmaxBal, we need to know that the set of 1b    *)
(* and 2b messages in bmsgs is finite.  This is asserted by the following  *)
(* invariant.  Note that the set bmsgs is not necessarily finite because   *)
(* we allow a Phase1c action to send an infinite number of 1c messages.    *)
(***************************************************************************)
bmsgsFinite ≜ IsFiniteSet(1bOr2bMsgs)

(***************************************************************************)
(* The following lemma is used to prove the invariance of bmsgsFinite.     *)
(***************************************************************************)
LEMMA FiniteMsgsLemma ≜
        ASSUME NEW m, bmsgsFinite, bmsgs' = bmsgs ∪ {m}
        PROVE  bmsgsFinite'
BY FS_AddElement DEF bmsgsFinite, 1bOr2bMsgs

(***************************************************************************)
(* Invariant 1bInv1 asserts that if (good) acceptor `a' has mCBal[a] # -1, *)
(* then there is a 1c message for ballot mCBal[a] and value mCVal[a] in    *)
(* the emulated execution of algorithm PCon.                               *)
(***************************************************************************)
1bInv1 ≜ ∀ m ∈ bmsgs  :
             ∧ m.type = "1b"
             ∧ m.acc ∈ Acceptor
             ⇒ ∀ r ∈ m.m2av :
                [type ↦ "1c", bal ↦ r.bal, val ↦ r.val] ∈ msgs

(***************************************************************************)
(* Invariant 1bInv2 asserts that an acceptor sends at most one 1b message  *)
(* for any ballot.                                                         *)
(***************************************************************************)
1bInv2 ≜ ∀ m1, m2 ∈ bmsgs  :
             ∧ m1.type = "1b"
             ∧ m2.type = "1b"
             ∧ m1.acc ∈ Acceptor
             ∧ m1.acc = m2.acc
             ∧ m1.bal = m2.bal
             ⇒ m1 = m2

(***************************************************************************)
(* Invariant 2avInv1 asserts that an acceptor sends at most one 2av        *)
(* message in any ballot.                                                  *)
(***************************************************************************)
2avInv1 ≜ ∀ m1, m2 ∈ bmsgs :
             ∧ m1.type = "2av"
             ∧ m2.type = "2av"
             ∧ m1.acc ∈ Acceptor
             ∧ m1.acc = m2.acc
             ∧ m1.bal = m2.bal
             ⇒ m1 = m2

(***************************************************************************)
(* Invariant 2avInv2 follows easily from the meaning (and setting) of      *)
(* 2avSent.                                                                *)
(***************************************************************************)
2avInv2 ≜ ∀ m ∈ bmsgs :
             ∧ m.type = "2av"
             ∧ m.acc ∈ Acceptor
             ⇒ ∃ r ∈ 2avSent[m.acc] : ∧ r.val = m.val
                                      ∧ r.bal ≥ m.bal

(***************************************************************************)
(* Invariant 2avInv3 asserts that an acceptor sends a 2av message only if  *)
(* the required 1c message exists in the emulated execution of             *)
(* algorithm PConf.                                                        *)
(***************************************************************************)
2avInv3 ≜ ∀ m ∈ bmsgs :
             ∧ m.type = "2av"
             ∧ m.acc ∈ Acceptor
             ⇒ [type ↦ "1c", bal ↦ m.bal, val ↦ m.val] ∈ msgs

(***************************************************************************)
(* Invariant maxBalInv is a simple consequence of the fact that an         *)
(* acceptor `a' sets maxBal[a] to b whenever it sends a 1b, 2av, or 2b     *)
(* message in ballot b.                                                    *)
(***************************************************************************)
maxBalInv ≜ ∀ m ∈ bmsgs :
               ∧ m.type ∈ {"1b", "2av", "2b"}
               ∧ m.acc ∈ Acceptor
               ⇒ m.bal ≤ maxBal[m.acc]

(***************************************************************************)
(* Invariant accInv asserts some simple relations between the variables    *)
(* local to an acceptor, as well as the fact that acceptor `a' sets        *)
(* maxCBal[a] to b and maxCVal[a] to v only if there is a ballot-b 1c      *)
(* message for value c in the simulated execution of the PCon              *)
(* algorithm.                                                              *)
(***************************************************************************)
accInv ≜ ∀ a ∈ Acceptor :
            ∀ r ∈ 2avSent[a] :
              ∧ r.bal ≤ maxBal[a]
              ∧ [type ↦ "1c", bal ↦ r.bal, val ↦ r.val] ∈ msgs

(***************************************************************************)
(* Invariant knowsSentInv simply asserts that for any acceptor `a',        *)
(* knowsSent[a] is a set of 1b messages that have actually been sent.      *)
(***************************************************************************)
knowsSentInv ≜ ∀ a ∈ Acceptor : knowsSent[a] ⊆ msgsOfType("1b")

Inv ≜
 TypeOK ∧ bmsgsFinite ∧ 1bInv1 ∧ 1bInv2 ∧ maxBalInv  ∧ 2avInv1 ∧ 2avInv2
   ∧ 2avInv3 ∧ accInv ∧ knowsSentInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now prove some simple lemmas that are useful for reasoning about     *)
(* PmaxBal.                                                                *)
(***************************************************************************)
LEMMA PMaxBalLemma3 ≜
        ASSUME TypeOK,
               bmsgsFinite,
               NEW a ∈ Acceptor
        PROVE  LET S ≜ {m.bal : m ∈ {ma ∈ bmsgs :
                                           ∧ ma.type ∈ {"1b", "2b"}
                                           ∧ ma.acc = a}}
               IN  ∧ IsFiniteSet(S)
                   ∧ S ∈ SUBSET Ballot
<1> DEFINE T ≜ {ma ∈ bmsgs : ∧ ma.type ∈ {"1b", "2b"}
                             ∧ ma.acc = a}
           S ≜ {m.bal : m ∈ T}
<1>1. IsFiniteSet(S)
  <2>1. IsFiniteSet(T)
    BY FS_Subset DEF bmsgsFinite, 1bOr2bMsgs
  <2>. QED
    BY <2>1, FS_Image, Isa
<1>. QED  BY <1>1, BMessageLemma DEF 1bMessage, 2bMessage, TypeOK

LEMMA PmaxBalLemma4 ≜
        ASSUME TypeOK,
               maxBalInv,
               bmsgsFinite,
               NEW a ∈ Acceptor
        PROVE  PmaxBal[a] ≤ maxBal[a]
<1> DEFINE SM ≜ {ma ∈ bmsgs : ∧ ma.type ∈ {"1b", "2b"}
                              ∧ ma.acc = a}
           S  ≜ {ma.bal : ma ∈ SM}
<1>1. PmaxBal[a] = MaxBallot(S)
  BY DEF PmaxBal, 1bOr2bMsgs
<1>2. ∧ IsFiniteSet(S)
      ∧ S ∈ SUBSET Ballot
  BY PMaxBalLemma3
<1>3. ∀ b ∈ S : b ≤ maxBal[a]
  BY DEF maxBalInv
<1>4. CASE S = {}
  <2>1. PmaxBal[a] = -1
    BY <1>2,  <1>1, <1>4, MaxBallotProp
  <2>. QED
    BY <2>1 DEF Ballot, TypeOK
<1>5. CASE S ≠ {}
  <2>1. MaxBallot(S) ∈ S
    BY <1>2,  <1>5,  MaxBallotProp, Zenon
  <2>2. QED
    BY <1>1, <1>3, <2>1
<1>6. QED
  BY <1>4, <1>5

LEMMA PmaxBalLemma5 ≜
        ASSUME TypeOK, bmsgsFinite, NEW a ∈ Acceptor
        PROVE  PmaxBal[a] ∈ Ballot ∪ {-1}
BY PMaxBalLemma3, MaxBallotProp DEF PmaxBal, 1bOr2bMsgs

-----------------------------------------------------------------------------
(***************************************************************************)
(* Now comes a bunch of useful lemmas.                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first prove that P!NextDef is a valid theorem and give it the name   *)
(* PNextDef.  This requires proving that the assumptions of module         *)
(* PConProof are satisfied by the refinement mapping.  Note that           *)
(* P!NextDef!: is an abbreviation for the statement of theorem P!NextDef   *)
(* -- that is, for the statement of theorem NextDef of module PConProof    *)
(* under the substitutions of the refinement mapping.                      *)
(***************************************************************************)
LEMMA PNextDef ≜ P!NextDef!:
<1>1. P!QA
  BY QuorumTheorem
<1>2. P!BallotAssump
  BY BallotAssump DEF Ballot, P!Ballot, ByzAcceptor
<1>3. QED
  BY P!NextDef, <1>1, <1>2, NoSetContainsEverything

(***************************************************************************)
(* For convenience, we define operators corresponding to subexpressions    *)
(* that appear in the definition of KnowsSafeAt.                           *)
(***************************************************************************)
KSet(a, b) ≜ {m ∈ knowsSent[a] : m.bal = b}
KS1(S) ≜ ∃ BQ ∈ ByzQuorum : ∀ a ∈ BQ :
             ∃ m ∈ S : m.acc = a ∧ m.mbal = -1
KS2(v,b,S) ≜ ∃ c ∈ 0 ‥ (b-1) :
   ∧ ∃ BQ ∈ ByzQuorum : ∀ a ∈ BQ :
         ∃ m ∈ S : ∧ m.acc = a
                   ∧ m.mbal ≤ c
                   ∧ (m.mbal = c) ⇒ (m.mval = v)
   ∧ ∃ WQ ∈ WeakQuorum : ∀ a ∈ WQ :
         ∃ m ∈ S : ∧ m.acc = a
                   ∧ ∃ r ∈ m.m2av : ∧ r.bal ≥ c
                                    ∧ r.val = v

(***************************************************************************)
(* The following lemma asserts the obvious relation between KnowsSafeAt    *)
(* and the top-level definitions KS1, KS2, and KSet.  The second conjunct  *)
(* is, of course, the primed version of the first.                         *)
(***************************************************************************)
LEMMA KnowsSafeAtDef ≜
        ∀ a, b, v :
           ∧ KnowsSafeAt(a, b, v) ⇔ KS1(KSet(a,b)) ∨ KS2(v, b, KSet(a, b))
           ∧ KnowsSafeAt(a, b, v)' ⇔ KS1(KSet(a,b)') ∨ KS2(v, b, KSet(a, b)')
  BY DEF KnowsSafeAt, KSet, KS1, KS2

LEMMA MsgsTypeLemma ≜
        ∀ m ∈ msgs : ∧ (m.type = "1a") ⇔ (m ∈ msgsOfType("1a"))
                     ∧ (m.type = "1b") ⇔ (m ∈ 1bmsgs)
                     ∧ (m.type = "1c") ⇔ (m ∈ 1cmsgs)
                     ∧ (m.type = "2a") ⇔ (m ∈ 2amsgs)
                     ∧ (m.type = "2b") ⇔ (m ∈ acceptorMsgsOfType("2b"))
BY DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, 2amsgs, acceptorMsgsOfType, msgs

(***************************************************************************)
(* The following lemma is the primed version of MsgsTypeLemma.  That is,   *)
(* its statement is just the statement of MsgsTypeLemma primed.  It        *)
(* follows from MsgsTypeLemma by the meta-theorem that if we can prove a   *)
(* state-predicate F as a (top-level) theorem, then we can deduce F'. This *)
(* is an instance of propositional temporal-logic reasoning. Alternatively *)
(* the lemma could be proved using the same reasoning used for the         *)
(* unprimed version of the theorem.                                        *)
(***************************************************************************)
LEMMA MsgsTypeLemmaPrime ≜
        ∀ m ∈ msgs' : ∧ (m.type = "1a") ⇔ (m ∈ msgsOfType("1a")')
                      ∧ (m.type = "1b") ⇔ (m ∈ 1bmsgs')
                      ∧ (m.type = "1c") ⇔ (m ∈ 1cmsgs')
                      ∧ (m.type = "2a") ⇔ (m ∈ 2amsgs')
                      ∧ (m.type = "2b") ⇔ (m ∈ acceptorMsgsOfType("2b")')
<1>1. MsgsTypeLemma'
  BY MsgsTypeLemma, PTL
<1>. QED
  BY <1>1

(***************************************************************************)
(* The following lemma describes how msgs is changed by the actions of the *)
(* algorithm.                                                              *)
(***************************************************************************)
LEMMA MsgsLemma ≜
TypeOK ⇒
    ∧ ∀ self ∈ Acceptor, b ∈ Ballot :
         Phase1b(self, b) ⇒
            msgs' = msgs ∪
                     {[type ↦ "1b", acc ↦ self, bal ↦ b,
                       mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]}
    ∧ ∀ self ∈ Acceptor, b ∈ Ballot :
         Phase2av(self, b) ⇒
            ∨ msgs' = msgs
            ∨ ∃ v ∈ Value :
                 ∧ [type ↦ "1c", bal ↦ b, val ↦ v] ∈ msgs
                 ∧ msgs' = msgs ∪ {[type ↦ "2a", bal ↦ b, val ↦ v]}
    ∧ ∀ self ∈ Acceptor, b ∈ Ballot :
          Phase2b(self, b) ⇒
             ∃ v ∈ Value :
               ∧ ∃ Q ∈ ByzQuorum :
                    ∀ a ∈ Q :
                       ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = v
                                                  ∧ m.acc = a
               ∧ msgs' = msgs ∪
                            {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
               ∧ bmsgs' = bmsgs ∪
                            {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
               ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
    ∧ ∀ self ∈ Acceptor, b ∈ Ballot :
          LearnsSent(self, b) ⇒
            ∃ S ∈ SUBSET {m ∈ msgsOfType("1c") : m.bal = b} :
                     msgs' = msgs ∪ S
    ∧ ∀ self ∈ Ballot :
         Phase1a(self) ⇒
           msgs' = msgs ∪ {[type ↦ "1a", bal ↦ self]}
    ∧ ∀ self ∈ Ballot :
         Phase1c(self) ⇒
           ∃ S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]:
              ∧ ∀ m ∈ S :
                    ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)
              ∧ msgs' = msgs ∪ S
    ∧ ∀ self ∈ FakeAcceptor : FakingAcceptor(self) ⇒ msgs' = msgs
<1> HAVE TypeOK

<1>1. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot, Phase1b(self,b)
      PROVE  msgs' = msgs ∪
                      {[type ↦ "1b", acc ↦ self, bal ↦ b,
                        mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]}
  <2> DEFINE m ≜ [type ↦ "1b", acc ↦ self, bal ↦ b,
                   m2av ↦ 2avSent[self],
                   mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]
  <2>1. bmsgs' = bmsgs ∪ {m} ∧ knowsSent' = knowsSent
    BY <1>1 DEF Phase1b
  <2>a. ∧ msgsOfType("1a")' =  msgsOfType("1a")
        ∧ 1bmsgs' = 1bmsgs ∪ {1bRestrict(m)}
        ∧ 1cmsgs' = 1cmsgs
        ∧ 2amsgs' = 2amsgs
        ∧ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <2>1 DEF msgsOfType, 1bmsgs, acceptorMsgsOfType, KnowsSafeAt, 1cmsgs, 2amsgs
  <2>. QED
    BY <2>a DEF msgs, 1bRestrict

<1>2. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot, Phase2av(self,b)
      PROVE  ∨ msgs' = msgs
             ∨ ∃ v ∈ Value :
                   ∧ [type ↦ "1c", bal ↦ b, val ↦ v] ∈ msgs
                   ∧ msgs' = msgs ∪ {[type ↦ "2a", bal ↦ b, val ↦ v]}
  <2>1. PICK m ∈ sentMsgs("1c", b) :
               ∧ KnowsSafeAt(self, b, m.val)
               ∧ bmsgs' = bmsgs ∪
                    {[type ↦ "2av", bal ↦ b, val ↦ m.val, acc ↦ self]}
    BY <1>2 DEF Phase2av
  <2>2. m = [type ↦ "1c", bal ↦ b, val ↦ m.val]
    BY BMessageLemma DEF sentMsgs, TypeOK, 1cMessage
  <2> DEFINE ma ≜ [type ↦ "2a", bal ↦ b, val ↦ m.val]
             mb ≜ [type ↦ "2av", bal ↦ b, val ↦ m.val, acc ↦ self]
  <2>3. SUFFICES ASSUME msgs' ≠ msgs
                 PROVE  ∧ m ∈ msgs
                        ∧ msgs' = msgs ∪ {ma}
    BY <2>2, BMessageLemma DEF sentMsgs, TypeOK, 1cMessage
  <2>4. m ∈ msgs
    BY <2>1, <2>2 DEF sentMsgs, 1cmsgs, msgsOfType, msgs
  <2>5. msgs' = msgs ∪ {ma}
    <3>1. knowsSent' = knowsSent
      BY <1>2 DEF Phase2av
    <3>2. ∧ msgsOfType("1a")' = msgsOfType("1a")
          ∧ 1bmsgs' = 1bmsgs
          ∧ 1cmsgs' = 1cmsgs
          ∧ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
      BY <2>1, <3>1 DEF msgsOfType, 1bmsgs, 1bRestrict, acceptorMsgsOfType, KnowsSafeAt, 1cmsgs
    <3>. QED
      BY <3>1, <3>2, <2>1, <2>3 DEF msgs, 2amsgs, msgsOfType, acceptorMsgsOfType
  <2>6. QED
    BY <2>4, <2>5

<1>3. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot, Phase2b(self, b)
      PROVE  ∃ v ∈ Value :
                ∧ ∃ Q ∈ ByzQuorum :
                      ∀ a ∈ Q :
                         ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = v
                                                    ∧ m.acc = a
                ∧ msgs' = msgs ∪
                             {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
                ∧ bmsgs' = bmsgs ∪
                             {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
                ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
  <2>1. PICK v ∈ Value :
               ∧ ∃ Q ∈ ByzQuorum :
                     ∀ a ∈ Q :
                        ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = v
                                                   ∧ m.acc = a
               ∧ bmsgs' = bmsgs ∪
                             {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
               ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
               ∧ knowsSent' = knowsSent
    BY <1>3, Zenon DEF Phase2b
  <2> DEFINE bm ≜ [type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]
  <2>2. ∧ msgsOfType("1a")' = msgsOfType("1a")
        ∧ 1bmsgs' = 1bmsgs
        ∧ 1cmsgs' = 1cmsgs
        ∧ 2amsgs' = 2amsgs
        ∧ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b") ∪ {bm}
    BY <2>1 DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt, 2amsgs, acceptorMsgsOfType
  <2>4. msgs' = msgs ∪ {bm}
    BY <2>2 DEF msgs
  <2>. QED
    BY <2>1, <2>4, Zenon

<1>4. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot, LearnsSent(self, b)
      PROVE  ∃ S ∈ SUBSET {m ∈ msgsOfType("1c") : m.bal = b} : msgs' = msgs ∪ S
  <2>1. ∧ msgsOfType("1a")' = msgsOfType("1a")
        ∧ 1bmsgs' = 1bmsgs
        ∧ 2amsgs' = 2amsgs
        ∧ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
    BY <1>4 DEF LearnsSent, msgsOfType, 1bmsgs, 1bRestrict, 2amsgs, acceptorMsgsOfType
  <2>. ∧ 1cmsgs ⊆ 1cmsgs'
       ∧ 1cmsgs' \ 1cmsgs ∈ SUBSET {m ∈ msgsOfType("1c") : m.bal = b}
    <3>1. bmsgs' = bmsgs
      BY <1>4 DEF LearnsSent
    <3>2. PICK S ∈ SUBSET sentMsgs("1b", b):
             knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] ∪ S]
      BY <1>4, Zenon DEF LearnsSent
    <3>3. ASSUME NEW m ∈ 1cmsgs
          PROVE  m ∈ 1cmsgs'
      BY <3>1, <3>2 DEF TypeOK, KnowsSafeAt, 1cmsgs, msgsOfType
    <3>4. ASSUME NEW m ∈ 1cmsgs', m ∉ 1cmsgs
          PROVE  m ∈ msgsOfType("1c") ∧ m.bal = b
      <4>1. m ∈ msgsOfType("1c")
        BY <3>1 DEF 1cmsgs, msgsOfType
      <4>2. PICK a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)'
        BY DEF 1cmsgs
      <4>3. ¬KnowsSafeAt(a, m.bal, m.val)
        BY <3>4, <4>1 DEF 1cmsgs
      <4>4. ∀ aa ∈ Acceptor, bb ∈ Ballot :
               ∀ mm ∈ KSet(aa, bb)' :
                   mm ∉ KSet(aa, bb) ⇒ bb = b
        BY <1>4, <3>2 DEF TypeOK, LearnsSent, TypeOK, sentMsgs, KSet
      <4>5. m.bal ∈ Ballot
        BY <4>1, BMessageLemma DEF 1cMessage, msgsOfType, TypeOK
      <4>6. CASE KS1(KSet(a,m.bal)') ∧ ¬KS1(KSet(a,m.bal))
        BY <4>6, <4>1, <4>4, <4>5 DEF KS1
      <4>7. CASE KS2(m.val, m.bal, KSet(a, m.bal)') ∧ ¬KS2(m.val, m.bal, KSet(a, m.bal))
        BY <4>7, <4>1, <4>4, <4>5 DEF KS2
      <4> QED
        BY <4>6, <4>7, <4>2, <4>3, KnowsSafeAtDef
    <3>5. QED
      BY <3>3, <3>4
  <2>. WITNESS 1cmsgs' \ 1cmsgs ∈ SUBSET {m ∈ msgsOfType("1c") : m.bal = b}
  <2>. QED
    BY <2>1 DEF msgs

<1>5. ASSUME NEW self ∈ Ballot, Phase1a(self)
      PROVE  msgs' = msgs ∪ {[type ↦ "1a", bal ↦ self]}
  BY <1>5 DEF Phase1a, msgs, msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt,
              2amsgs, acceptorMsgsOfType

<1>6. ASSUME NEW  self ∈ Ballot, Phase1c(self)
      PROVE  ∃ S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                 ∧ ∀ m ∈ S :
                      ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)
                 ∧ msgs' = msgs ∪ S
  <2>1. PICK S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value] :
             ∧ bmsgs' = bmsgs ∪ S
             ∧ knowsSent' = knowsSent
    BY <1>6 DEF Phase1c
  <2> DEFINE SS ≜ {m ∈ S : ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)}
  <2> SUFFICES msgs' = msgs ∪ SS
    BY <2>1, Zenon
  <2>2. ∧ msgsOfType("1a")' = msgsOfType("1a")
        ∧ 1bmsgs' = 1bmsgs
        ∧ 1cmsgs' = 1cmsgs ∪ SS
        ∧ 2amsgs' = 2amsgs
        ∧ acceptorMsgsOfType("2b")' = acceptorMsgsOfType("2b")
   BY <2>1 DEF msgsOfType, 1bmsgs, 1bRestrict, 1cmsgs, KnowsSafeAt, 2amsgs, acceptorMsgsOfType
  <2>3. QED
    BY <2>2 DEF msgs

<1>7. ASSUME NEW  self ∈ FakeAcceptor, FakingAcceptor(self)
      PROVE  msgs' = msgs
  BY <1>7, BQA DEF FakingAcceptor, msgs, 1bMessage, 2avMessage, 2bMessage,
       msgsOfType, 1cmsgs, KnowsSafeAt, 1bmsgs, 2amsgs, acceptorMsgsOfType, msgsOfType

<1>9. QED
  BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, Zenon

-----------------------------------------------------------------------------
(***************************************************************************)
(* We now come to the proof of invariance of our inductive invariant Inv.  *)
(***************************************************************************)
THEOREM Invariance ≜ Spec ⇒ □Inv
<1>1. Init ⇒ Inv
  BY FS_EmptySet DEF Init, Inv, TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
         maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv

<1>2. Inv ∧ [Next]_vars ⇒ Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE Inv'
    OBVIOUS
  <2>1. ASSUME NEW self ∈ Acceptor,
               NEW b ∈ Ballot,
               ∨ Phase1b(self, b)
               ∨ Phase2av(self, b)
               ∨ Phase2b(self,b)
               ∨ LearnsSent(self, b)
        PROVE  Inv'
    <3>1. CASE Phase1b(self, b)
      <4> DEFINE mb ≜ [type  ↦ "1b", bal ↦ b, acc ↦ self,
                        m2av ↦ 2avSent[self],
                        mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]
                 mc ≜ [type ↦ "1b", acc ↦ self, bal ↦ b,
                        mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]
      <4>1. msgs' = msgs ∪ {mc}
        BY <3>1, MsgsLemma DEF Inv
      <4>2. TypeOK'
        BY <3>1 DEF Inv, TypeOK, BMessage, 1bMessage, ByzAcceptor, Phase1b
      <4>3. bmsgsFinite'
        BY <3>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite, Phase1b
      <4>4. 1bInv1'
        BY <3>1, <4>1, IsaT(100) DEF Phase1b, 1bInv1, Inv, accInv
      <4>5. 1bInv2'
        BY <3>1 DEF Phase1b, 1bInv2, Inv, maxBalInv, TypeOK, 1bMessage, Ballot
      <4>6. maxBalInv'
        BY <3>1, BMessageLemma DEF Phase1b, maxBalInv, Ballot, Inv, TypeOK,
           1bMessage, 2avMessage, 2bMessage
      <4>7. 2avInv1'
        BY <3>1 DEF Phase1b, Inv, 2avInv1
      <4>8. 2avInv2'
        BY <3>1 DEF Phase1b, Inv, 2avInv2
      <4>9. 2avInv3'
        BY <3>1, <4>1 DEF Phase1b, Inv, 2avInv3
      <4>10. accInv'
        <5> SUFFICES ASSUME NEW a ∈ Acceptor,
                            NEW r ∈ 2avSent[a]
                     PROVE  ∧ r.bal ≤ maxBal'[a]
                            ∧ [type ↦ "1c", bal ↦ r.bal, val ↦ r.val]
                                   ∈ msgs'
          BY <3>1, Zenon DEF accInv, Phase1b
        <5> [type ↦ "1c", bal ↦ r.bal, val ↦ r.val] ∈ msgs'
          BY <3>1, MsgsLemma DEF Inv, accInv
        <5> QED
          BY <3>1 DEF Phase1b, Inv, Ballot, TypeOK, accInv
      <4>11. knowsSentInv'
        BY <3>1 DEF Phase1b, Inv, knowsSentInv, msgsOfType
      <4>12. QED
        BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
    <3>2. CASE Phase2av(self, b)
      <4>1. PICK mc ∈ sentMsgs("1c", b) :
                   ∧ KnowsSafeAt(self, b, mc.val)
                   ∧ bmsgs' = bmsgs ∪
                                 {[type ↦ "2av", bal ↦ b,
                                   val ↦ mc.val, acc ↦ self]}
                   ∧ 2avSent' = [2avSent EXCEPT
                        ![self] = {r ∈ 2avSent[self] : r.val ≠ mc.val}
                                    ∪ {[val ↦ mc.val, bal ↦ b]}]
        BY <3>2, Zenon DEF Phase2av
      <4>2. mc = [type ↦ "1c", bal ↦ mc.bal, val ↦ mc.val]
        BY <4>1, BMessageLemma DEF sentMsgs, Inv, TypeOK, 1cMessage
      <4> DEFINE mb ≜ [type ↦ "2av", bal ↦ b,
                        val ↦ mc.val, acc ↦ self]
                 mmc(v) ≜ [type ↦ "1c", bal ↦ b, val ↦ v]
                 ma(v) ≜ [type ↦ "2a", bal ↦ b, val ↦ v]
      <4>3. ∨ msgs' = msgs
            ∨ ∃ v ∈ Value :
                 ∧ mmc(v) ∈ msgs
                 ∧ msgs' = msgs ∪ {ma(v)}
        BY <3>2, MsgsLemma, Zenon DEF Inv
      <4>4. msgs ⊆ msgs'
        BY <4>3, Zenon
      <4>5. TypeOK'
        BY <3>2, <4>1, BMessageLemma
           DEF sentMsgs, Inv, TypeOK, 1cMessage, Phase2av, 2avMessage, ByzAcceptor, BMessage
      <4>6. bmsgsFinite'
        BY <4>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite
      <4>7. 1bInv1'
        BY <3>2, <4>1, <4>3, IsaT(100) DEF Phase2av, 1bInv1, Inv
      <4>8. 1bInv2'
        BY <4>1 DEF Inv, 1bInv2
      <4>9. maxBalInv'
        BY <3>2, <4>1, BMessageLemma
           DEF Phase2av, maxBalInv, Ballot, Inv, TypeOK, 1bMessage, 2avMessage, 2bMessage
      <4>10. 2avInv1'
        BY <3>2, <4>1 DEF Phase2av, Inv, 2avInv1, 2avInv2, TypeOK, 1bMessage, Ballot
      <4>11. 2avInv2'
        <5>1. SUFFICES ASSUME NEW m ∈ bmsgs',
                              2avInv2!(m)!1
                       PROVE  ∃ r ∈ 2avSent'[m.acc] : ∧ r.val = m.val
                                                      ∧ r.bal ≥ m.bal
          BY DEF 2avInv2
        <5>2. CASE m.acc = self
          <6>1. CASE m = mb
            BY <4>1, <6>1, Isa DEF Inv, TypeOK, Ballot
          <6>2. CASE m ≠ mb
            <7>1. m ∈ bmsgs
              BY <4>1, <6>2
            <7>2. PICK r ∈ 2avSent[m.acc] : ∧ r.val = m.val
                                            ∧ r.bal ≥ m.bal
              BY <5>1, <7>1 DEF Inv, 2avInv2
            <7>3. CASE r.val = mc.val
              <8>. DEFINE rr ≜ [val ↦ mc.val, bal ↦ b]
              <8>. rr ∈ 2avSent'[m.acc]
                BY <4>1, <5>2 DEF Inv, TypeOK
              <8>. WITNESS rr ∈ 2avSent'[m.acc]
              <8>. QED
                BY <7>2, <7>3, <5>2, <5>1, <3>2, BMessageLemma
                   DEF Phase2av, Inv, TypeOK, accInv, Ballot, 2avMessage
            <7>4. CASE r.val ≠ mc.val
              BY <7>2, <4>1, <5>2, <7>4 DEF Inv, TypeOK
            <7>5. QED
              BY <7>3, <7>4
          <6>3. QED
            BY <6>1, <6>2
        <5>3. CASE m.acc ≠ self
          BY <5>3, <5>1, <4>1, BMessageLemma DEF Inv, TypeOK, 2avInv2, 2avMessage
        <5>4. QED
          BY <5>2, <5>3
      <4>12. 2avInv3'
        BY <4>1, <4>2, <4>4 DEF Inv, 2avInv3, sentMsgs, msgs, 1cmsgs, msgsOfType
      <4>13. accInv'
        <5>1. SUFFICES ASSUME NEW a ∈ Acceptor,
                              NEW r ∈ 2avSent'[a]
                       PROVE  ∧ r.bal ≤ maxBal'[a]
                              ∧ [type ↦ "1c", bal ↦ r.bal, val ↦ r.val]
                                    ∈ msgs'
          BY Zenon DEF accInv
        <5>2. CASE r ∈ 2avSent[a]
          BY <5>2, <4>4, <4>5, <3>2 DEF Phase2av, Inv, TypeOK, accInv, Ballot
        <5>3. CASE r ∉ 2avSent[a]
          BY <5>3, <3>2, <4>1, <4>2, <4>4
             DEF Phase2av, Inv, TypeOK, sentMsgs, msgsOfType, msgs, 1cmsgs, Ballot
        <5>4. QED
          BY <5>2, <5>3
      <4>14. knowsSentInv'
        BY <3>2, <4>1 DEF Phase2av, Inv, knowsSentInv, msgsOfType
      <4>15. QED
        BY <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF Inv
    <3>3. CASE Phase2b(self, b)
      <4>1. PICK v ∈ Value :
              ∧ ∃ Q ∈ ByzQuorum :
                    ∀ a ∈ Q :
                       ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = v
                                                  ∧ m.acc = a
              ∧ msgs' = msgs ∪
                            {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
              ∧ bmsgs' = (bmsgs ∪
                     {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]})
              ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
        BY <3>3, MsgsLemma DEF Inv
      <4> DEFINE mb ≜ [type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]
      <4>2. TypeOK'
        BY <3>3, <4>1 DEF Phase2b, Inv, TypeOK, BMessage, 2bMessage, ByzAcceptor
      <4>3. bmsgsFinite'
         BY <4>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite
      <4>4. 1bInv1'
        BY <4>1, Isa DEF Inv, 1bInv1
      <4>5. 1bInv2'
        BY <4>1 DEF Inv, 1bInv2
      <4>6. maxBalInv'
        BY <3>3, <4>1, <4>2, BMessageLemma
           DEF Phase2b, Inv, maxBalInv, TypeOK, Ballot, 1bMessage, 2avMessage, 2bMessage
      <4>7. 2avInv1'
        BY <4>1 DEF Inv, 2avInv1
      <4>8. 2avInv2'
        BY <3>3, <4>1 DEF Phase2b, Inv, TypeOK, 2avInv2
      <4>9. 2avInv3'
        BY <4>1 DEF Inv, 2avInv3
      <4>10. accInv'
        <5> SUFFICES ASSUME NEW a ∈ Acceptor,
                            NEW r ∈ 2avSent[a]
                     PROVE  ∧ r.bal ≤ maxBal'[a]
                            ∧ [type ↦ "1c", bal ↦ r.bal, val ↦ r.val]
                                   ∈ msgs'
          BY <3>3, Zenon DEF accInv, Phase2b
        <5> [type ↦ "1c", bal ↦ r.bal, val ↦ r.val] ∈ msgs'
          BY <3>3, MsgsLemma DEF Inv, accInv
        <5> QED
          BY <3>3 DEF Phase2b, Inv, Ballot, TypeOK, accInv
      <4>11. knowsSentInv'
        BY <3>3, <4>1 DEF Phase2b, Inv, knowsSentInv, msgsOfType
      <4>12. QED
        BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
    <3>4. CASE LearnsSent(self, b)
      <4>1. PICK MS : ∧ MS ⊆ {m ∈ msgsOfType("1c") : m.bal = b}
                      ∧ msgs' = msgs ∪ MS
        BY <3>4, MsgsLemma, Zenon DEF Inv
      <4>2. PICK S :
              ∧ S ⊆ sentMsgs("1b", b)
              ∧ knowsSent' =
                  [knowsSent EXCEPT ![self] = knowsSent[self] ∪ S]
        BY <3>4, Zenon DEF LearnsSent
      <4>3. TypeOK'
        BY <3>4, <4>2, BMessageLemma DEF Inv, TypeOK, sentMsgs, LearnsSent
      <4>4. bmsgsFinite'
        BY <3>4 DEF LearnsSent, Inv, bmsgsFinite, 1bOr2bMsgs
      <4>5. 1bInv1'
        BY <3>4, <4>1, Zenon DEF LearnsSent, Inv, 1bInv1
      <4>6. 1bInv2'
        BY <3>4 DEF LearnsSent, Inv, 1bInv2
      <4>7. maxBalInv'
        BY <3>4 DEF LearnsSent, Inv, maxBalInv
      <4>8. 2avInv1'
        BY <3>4 DEF LearnsSent, Inv, 2avInv1
      <4>9. 2avInv2'
        BY <3>4 DEF LearnsSent, Inv, 2avInv2
      <4>10. 2avInv3'
        BY <3>4, <4>1 DEF LearnsSent, Inv, 2avInv3
      <4>11. accInv'
        BY <3>4, <4>1, Zenon DEF LearnsSent, Inv, accInv
      <4>12. knowsSentInv'
        BY <3>4, <4>2 DEF LearnsSent, Inv, TypeOK, knowsSentInv, sentMsgs, msgsOfType
      <4>13. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12 DEF Inv
    <3>5. QED
      BY <2>1, <3>1, <3>2, <3>3, <3>4
  <2>2. ASSUME NEW self ∈ Ballot,
               ∨ Phase1a(self)
               ∨ Phase1c(self)
        PROVE  Inv'
    <3>1. CASE Phase1a(self)
      <4> DEFINE ma ≜ [type ↦ "1a", bal ↦ self]
      <4>1. msgs' = msgs ∪ {ma}
        BY <3>1, MsgsLemma DEF Inv
      <4>2. TypeOK'
        BY <3>1 DEF Phase1a, Inv, TypeOK, BMessage, 1aMessage
      <4>3. bmsgsFinite'
        BY <3>1, FiniteMsgsLemma, Zenon DEF Inv, bmsgsFinite, Phase1a
      <4>4. 1bInv1'
        BY <3>1, <4>1, Isa DEF Phase1a, Inv, 1bInv1
      <4>5. 1bInv2'
        BY <3>1 DEF Phase1a, Inv, 1bInv2
      <4>6. maxBalInv'
        BY <3>1 DEF Phase1a, Inv, maxBalInv
      <4>7. 2avInv1'
        BY <3>1 DEF Phase1a, Inv, 2avInv1
      <4>8. 2avInv2'
        BY <3>1 DEF Phase1a, Inv, 2avInv2
      <4>9. 2avInv3'
        BY <3>1, <4>1 DEF Phase1a, Inv, 2avInv3
      <4>10. accInv'
        BY <3>1, <4>1, Zenon DEF Phase1a, Inv, accInv
      <4>11. knowsSentInv'
        BY <3>1 DEF Inv, knowsSentInv, msgsOfType, Phase1a
      <4>12. QED
        BY <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11 DEF Inv
    <3>2. CASE Phase1c(self)
      <4>1. PICK S : ∧ S ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]
                     ∧ bmsgs' = bmsgs ∪ S
        BY <3>2 DEF Phase1c
      <4>2. PICK MS :
               ∧ MS ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value]
               ∧ ∀ m ∈ MS :
                    ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)
               ∧ msgs' = msgs ∪ MS
        BY <3>2, MsgsLemma DEF Inv
      <4>3. TypeOK'
        BY <3>2, <4>1 DEF Phase1c, Inv, TypeOK, BMessage, 1cMessage
      <4>4. bmsgsFinite'
        BY <4>1 DEF Inv, bmsgsFinite, 1bOr2bMsgs
      <4>5. 1bInv1'
        BY <3>2, <4>2, Zenon DEF Phase1c, Inv, 1bInv1
      <4>6. 1bInv2'
        BY <4>1 DEF Inv, 1bInv2
      <4>7. maxBalInv'
        BY <3>2 DEF Phase1c, Inv, maxBalInv
      <4>8. 2avInv1'
        BY <4>1 DEF Inv, 2avInv1
      <4>9. 2avInv2'
        BY <3>2 DEF Phase1c, Inv, 2avInv2
      <4>10. 2avInv3'
        BY <3>2, <4>2 DEF Phase1c, Inv, 2avInv3
      <4>11. accInv'
        BY <3>2, <4>2, Zenon DEF Phase1c, Inv, accInv
      <4>12. knowsSentInv'
        BY <3>2 DEF Inv, knowsSentInv, msgsOfType, Phase1c
      <4>13. QED
        BY <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10, <4>11, <4>12 DEF Inv
    <3>3. QED
      BY <3>1, <3>2, <2>2
  <2>3. ASSUME NEW self ∈ FakeAcceptor,
               FakingAcceptor(self)
        PROVE  Inv'
    <3>1. PICK m ∈ 1bMessage ∪ 2avMessage ∪ 2bMessage :
                 ∧ m.acc ∉ Acceptor
                 ∧ bmsgs' = bmsgs ∪ {m}
      BY <2>3, BQA DEF FakingAcceptor
    <3>2. msgs' = msgs
      BY <2>3, MsgsLemma DEF Inv
    <3>3. TypeOK'
      BY <2>3, <3>1 DEF Inv, TypeOK, BMessage, FakingAcceptor
    <3>4. bmsgsFinite'
      BY <3>1, FiniteMsgsLemma DEF Inv, TypeOK
    <3>5. 1bInv1'
      BY <3>1, <3>2, Zenon DEF Inv, 1bInv1
    <3>6. 1bInv2'
      BY <3>1 DEF Inv, 1bInv2
    <3>7. maxBalInv'
      BY <2>3, <3>1 DEF Inv, maxBalInv, FakingAcceptor
    <3>8. 2avInv1'
      BY <3>1 DEF Inv, 2avInv1
    <3>9. 2avInv2'
      BY <2>3, <3>1 DEF Inv, 2avInv2, FakingAcceptor
    <3>10. 2avInv3'
      BY <3>1, <3>2 DEF Inv, 2avInv3
    <3>11. accInv'
      BY <2>3, <3>2, Zenon DEF Inv, accInv, FakingAcceptor
    <3>12. knowsSentInv'
      BY <2>3, <3>1 DEF Inv, knowsSentInv, msgsOfType, FakingAcceptor
    <3>13. QED
      BY <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10, <3>11, <3>12 DEF Inv
  <2>4. ASSUME UNCHANGED vars
        PROVE  Inv'
    <3> USE UNCHANGED vars DEF Inv, vars
    <3> msgs = msgs'
      BY DEF msgs, msgsOfType, 1bmsgs, 1bRestrict, acceptorMsgsOfType, 1cmsgs,
       KnowsSafeAt, 2amsgs
    <3> QED
      BY DEF TypeOK, bmsgsFinite, 1bOr2bMsgs, 1bInv1, 1bInv2,
         maxBalInv, 2avInv1, 2avInv2, 2avInv3, accInv, knowsSentInv, msgsOfType
  <2>5. QED
    BY <2>1, <2>2, <2>3, <2>4, NextDef

<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* We next use the invariance of Inv to prove that algorithm BPCon         *)
(* implements algorithm PCon under the refinement mapping                  *)
(* defined by the INSTANCE statement above.                                *)
(***************************************************************************)
AbstractSpec ≜ P!Spec
THEOREM Spec ⇒ P!Spec
<1>1. Init ⇒ P!Init
  <2>. HAVE Init
  <2>1. MaxBallot({}) = -1
    BY MaxBallotProp, FS_EmptySet
  <2>2. P!Init!1 ∧ P!Init!2 ∧ P!Init!3
    BY <2>1 DEF Init, PmaxBal, 1bOr2bMsgs, None, P!None
  <2>3. msgs = {}
    BY BQA DEF Init, msgsOfType, acceptorMsgsOfType, 1bmsgs, 1cmsgs, 2amsgs, Quorum, msgs
  <2>4. QED
    BY <2>2, <2>3 DEF  P!Init

<1>2. Inv ∧ Inv' ∧ [Next]_vars ⇒ [P!Next]_P!vars
  <2> InvP ≜ Inv'
  <2> SUFFICES ASSUME Inv, InvP, Next
               PROVE  P!TLANext ∨ P!vars' = P!vars
    <3> UNCHANGED vars ⇒ UNCHANGED P!vars
      BY DEF vars, P!vars, PmaxBal, 1bOr2bMsgs, msgs, msgsOfType, acceptorMsgsOfType,
             1bmsgs, 2amsgs, 1cmsgs, KnowsSafeAt
    <3> QED
      BY PNextDef DEF Inv, P!ProcSet, P!Init, Ballot, P!Ballot
  <2> HIDE DEF InvP
  <2>2. ∀ a ∈ Acceptor : PmaxBal[a] ∈ Ballot ∪ {-1}
    BY PMaxBalLemma3, MaxBallotProp DEF Inv, PmaxBal, 1bOr2bMsgs
  <2>3. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot,
               Phase1b(self, b)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. msgs' = msgs ∪ {[type ↦ "1b", acc ↦ self, bal ↦ b,
                              mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]}
      BY <2>3, MsgsLemma DEF Inv
    <3>2. P!sentMsgs("1a", b) ≠ {}
      BY <2>3 DEF Phase1b, sentMsgs, msgsOfType, msgs, P!sentMsgs
    <3>3. UNCHANGED ⟨maxVBal, maxVVal⟩
      BY <2>3 DEF Phase1b
    <3>4. b > PmaxBal[self]
      BY <2>2, <2>3, PmaxBalLemma4 DEF Phase1b, Inv, TypeOK, Ballot
    <3>5. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
      <4> DEFINE m ≜ [type  ↦ "1b", bal ↦ b, acc ↦ self,
                       m2av ↦ 2avSent[self],
                       mbal ↦ maxVBal[self], mval ↦ maxVVal[self]]
                 mA(a) ≜ {ma ∈ bmsgs : ∧ ma.type ∈ {"1b", "2b"}
                                       ∧ ma.acc = a}
                 S(a) ≜ {ma.bal : ma ∈ mA(a)}
      <4>1. bmsgs' = bmsgs ∪ {m}
        BY <2>3 DEF Phase1b
      <4>2. mA(self)' = mA(self) ∪ {m}
        BY <4>1
      <4>3. ∧ PmaxBal = [a ∈ Acceptor ↦ MaxBallot(S(a))]
            ∧ PmaxBal' = [a ∈ Acceptor ↦ MaxBallot(S(a))']
        BY DEF PmaxBal, 1bOr2bMsgs
      <4> HIDE DEF mA
      <4>4. S(self)' = S(self) ∪ {b}
        BY <4>2, Isa
      <4>5. MaxBallot(S(self) ∪ {b}) = b
        <5> DEFINE SS ≜ S(self) ∪ {b}
        <5>1. IsFiniteSet(S(self))
          <6>. IsFiniteSet(mA(self))
            BY FS_Subset DEF Inv, bmsgsFinite, mA, 1bOr2bMsgs
          <6>. QED
            BY FS_Image, Isa
        <5>2. IsFiniteSet(SS)
          BY <5>1, FS_AddElement
        <5>3. S(self) ⊆ Ballot ∪ {-1}
          BY BMessageLemma DEF mA, Inv, TypeOK, 1bMessage, 2bMessage
        <5>4. ∀ x ∈ SS : b ≥ x
          BY <3>4, <4>3, <5>1, <5>3, MaxBallotProp, Z3T(10) DEF Ballot
        <5>5. QED
          BY <5>2, <5>3, <5>4, MaxBallotLemma1
      <4>6. ∀ a ∈ Acceptor : a ≠ self ⇒ S(a)' = S(a)
        BY <4>1 DEF mA
      <4>7. QED
        BY <4>3, <4>4, <4>5, <4>6, Zenon DEF PmaxBal, 1bOr2bMsgs
    <3>6. QED
       BY <3>1, <3>2, <3>3, <3>4, <3>5, Zenon DEF P!TLANext, P!Ballot, Ballot, P!Phase1b
  <2>4. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot,
               Phase2av(self, b)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. PmaxBal' = PmaxBal
      <4> DEFINE mm(m) ≜ [type ↦ "2av", bal ↦ b,
                           val ↦ m.val, acc ↦ self]
      <4>1. PICK m : bmsgs' = bmsgs ∪ {mm(m)}
        BY <2>4  DEF Phase2av
      <4>2. mm(m).type = "2av"
        OBVIOUS
      <4> QED
         BY <4>1, <4>2, PmaxBalLemma1, Zenon
    <3>2. CASE msgs' = msgs
       BY <3>1, <3>2, <2>4 DEF Phase2av, P!vars
    <3>3. CASE ∧ msgs' ≠ msgs
               ∧ ∃ v ∈ Value :
                    ∧ [type ↦ "1c", bal ↦ b, val ↦ v] ∈ msgs
                    ∧ msgs' = msgs ∪ {[type ↦ "2a", bal ↦ b, val ↦ v]}
      <4>1. PICK v ∈ Value :
                 ∧ [type ↦ "1c", bal ↦ b, val ↦ v] ∈ msgs
                 ∧ msgs' = msgs ∪ {[type ↦ "2a", bal ↦ b, val ↦ v]}
        BY <3>3
      <4>2. P!sentMsgs("2a", b) = {}
        <5>1. SUFFICES ASSUME NEW m ∈ P!sentMsgs("2a", b)
                       PROVE  m = [type ↦ "2a", bal ↦ b, val ↦ v]
          BY <3>3, <4>1 DEF P!sentMsgs
        <5>2. ∧ m ∈ 2amsgs
              ∧ m.type = "2a"
              ∧ m.bal = b
          BY MsgsTypeLemma DEF P!sentMsgs
        <5>3. PICK Q ∈ Quorum :
                     ∀ a ∈ Q :
                       ∃ mav ∈ acceptorMsgsOfType("2av") :
                         ∧ mav.acc = a
                         ∧ mav.bal = b
                         ∧ mav.val = m.val
          BY <5>2 DEF 2amsgs
        <5>4. PICK Q2 ∈ Quorum :
                     ∀ a ∈ Q2 :
                       ∃ m2av ∈ acceptorMsgsOfType("2av")' :
                         ∧ m2av.acc = a
                         ∧ m2av.bal = b
                         ∧ m2av.val = v
          BY <4>1, MsgsTypeLemmaPrime, Isa DEF 2amsgs
        <5>5. PICK a ∈ Q ∩ Q2 : a ∈ Acceptor
          BY QuorumTheorem
        <5>6. PICK mav ∈ acceptorMsgsOfType("2av") :
                         ∧ mav.acc = a
                         ∧ mav.bal = b
                         ∧ mav.val = m.val
          BY <5>3, <5>5
        <5>7. PICK m2av ∈ acceptorMsgsOfType("2av")' :
                      ∧ m2av.acc = a
                      ∧ m2av.bal = b
                      ∧ m2av.val = v
          BY <5>4, <5>5
        <5>8. mav ∈ acceptorMsgsOfType("2av")'
          BY <2>4 DEF acceptorMsgsOfType, msgsOfType, Phase2av
        <5>9. m.val = v
          BY <5>5, <5>6, <5>7, <5>8 DEF 2avInv1, InvP, Inv, acceptorMsgsOfType, msgsOfType
        <5>10. QED
          BY <5>2, <5>9 DEF 2amsgs
      <4>4. QED
        BY <2>4, <3>1, <4>1, <4>2 DEF P!TLANext, P!Phase2a, Phase2av, Ballot, P!Ballot
    <3>4.∨ msgs' = msgs
         ∨ (∧ msgs' ≠ msgs
            ∧ ∃ v ∈ Value :
                   ∧ [type ↦ "1c", bal ↦ b, val ↦ v] ∈ msgs
                   ∧ msgs' = msgs ∪ {[type ↦ "2a", bal ↦ b, val ↦ v]})
      BY MsgsLemma, <2>4, Zenon DEF Inv
    <3>5. QED
      BY <3>2, <3>3, <3>4
  <2>5. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot,
               Phase2b(self, b)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. PmaxBal[self] ≤ b
      <4>1. PmaxBal[self] ≤ maxBal[self]
        BY PmaxBalLemma4 DEF Inv
      <4>2. maxBal[self] ≤ b
        BY <2>5 DEF Phase2b
      <4>3. QED
        BY <4>1, <4>2, PmaxBalLemma5 DEF Inv, TypeOK, Ballot
    <3>2. PICK v ∈ Value :
                 ∧ ∃ Q ∈ ByzQuorum :
                      ∀ a ∈ Q :
                        ∃ m ∈ sentMsgs("2av", b) : ∧ m.val = v
                                                   ∧ m.acc = a
                 ∧ msgs' = msgs ∪
                            {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
                 ∧ bmsgs' = bmsgs ∪
                            {[type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]}
                 ∧ maxVVal' = [maxVVal EXCEPT ![self] = v]
      BY <2>5, MsgsLemma DEF Inv
    <3> DEFINE m ≜ [type ↦ "2a", bal ↦ b, val ↦ v]
               m2b ≜ [type ↦ "2b", acc ↦ self, bal ↦ b, val ↦ v]
    <3>3. m ∈ P!sentMsgs("2a", b)
      <4>1. PICK Q ∈ Quorum :
                   ∀ a ∈ Q :
                      ∃ mm ∈ sentMsgs("2av", b) : ∧ mm.val = v
                                                  ∧ mm.acc = a
        BY <3>2, Isa DEF Quorum
      <4>2. m ∈ 2amsgs
        BY <4>1 DEF sentMsgs, Quorum, acceptorMsgsOfType, msgsOfType, 2amsgs
      <4>3. QED
        BY <4>2 DEF P!sentMsgs, msgs
    <3>4. PmaxBal' = [PmaxBal EXCEPT ![self] = b]
      <4>1.  ASSUME NEW a ∈ Acceptor,
                    a ≠ self
             PROVE  PmaxBal'[a] = PmaxBal[a]
        BY <3>2, <4>1, PmaxBalLemma2, m2b.acc = self, Zenon
      <4>2. PmaxBal'[self] = b
        <5> DEFINE S ≜ {mm.bal : mm ∈ {ma ∈ bmsgs :
                                           ∧ ma.type ∈ {"1b", "2b"}
                                           ∧ ma.acc = self}}
                   T ≜ S ∪ {m2b.bal}
        <5>1. IsFiniteSet(S) ∧ (S ∈ SUBSET Ballot)
          BY PMaxBalLemma3 DEF Inv
        <5>2. IsFiniteSet(T) ∧ (T ∈ SUBSET Ballot)
          BY <5>1, FS_AddElement
        <5>3. PmaxBal[self] = MaxBallot(S)
          BY DEF PmaxBal, 1bOr2bMsgs
        <5>4. PmaxBal'[self] = MaxBallot(T)
          BY <3>2, Zenon DEF PmaxBal, 1bOr2bMsgs
        <5> HIDE DEF S
        <5>5. CASE S = {}
          <6> MaxBallot({b}) = b
            BY FS_Singleton, MaxBallotLemma1, Isa DEF Ballot
          <6> QED
            BY <5>4, <5>5
        <5>6. CASE S ≠ {}
          <6> ∀ bb ∈ T : b ≥ bb
            BY <3>1, <5>1, <5>3, MaxBallotProp, PmaxBalLemma5 DEF Inv, Ballot
          <6> QED
            BY <5>2, <5>4, MaxBallotLemma1
        <5>7. QED
          BY <5>5, <5>6
      <4>3. QED
        BY <4>1, <4>2, Zenon DEF PmaxBal, 1bOr2bMsgs
    <3>5. ∧ maxVBal' = [maxVBal EXCEPT ![self] = b]
          ∧ maxVVal' = [maxVVal EXCEPT ![self] = m.val]
      BY <2>5, <3>2, Zenon DEF Phase2b
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, Zenon
         DEF P!TLANext, P!Phase2b, Ballot, P!Ballot
  <2>6. ASSUME NEW self ∈ Acceptor, NEW b ∈ Ballot,
               LearnsSent(self, b)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. PICK SM ∈ SUBSET {m ∈ msgsOfType("1c") : m.bal = b} :
                        msgs' = msgs ∪ SM
      BY <2>6, MsgsLemma DEF Inv
    <3> DEFINE S ≜ {m.val : m ∈ SM}
    <3>2. S ∈ SUBSET Value
      BY BMessageLemma DEF Inv, TypeOK, msgsOfType, 1cMessage
    <3>3. msgs' = msgs ∪ {[type ↦ "1c", bal ↦ b, val ↦ v] : v ∈ S}
      BY <3>1, BMessageLemma DEF Inv, TypeOK, msgsOfType, 1cMessage
    <3>4. ASSUME NEW v ∈ S
          PROVE  ∃ Q ∈ Quorum : P!ShowsSafeAt(Q, b, v)
      <4>1. PICK ac ∈ Acceptor : KnowsSafeAt(ac, b, v)'
        BY <3>1, MsgsTypeLemmaPrime DEF msgsOfType, 1cmsgs
      <4>2. bmsgs' = bmsgs
        BY <2>6 DEF LearnsSent
      <4>  DEFINE Q(BQ) ≜ BQ ∩ Acceptor
                  SS ≜ {m ∈ knowsSent'[ac] : m.bal = b}
                  SQ(BQ) ≜ {1bRestrict(mm) :
                               mm ∈ {m ∈ SS : m.acc ∈ Q(BQ)}}
                  Q1b(BQ) ≜ {m ∈ P!sentMsgs("1b", b) : m.acc ∈ Q(BQ)}
      <4>3. ASSUME NEW BQ ∈ ByzQuorum,
                   ∀ a ∈ BQ : ∃ m ∈ SS : m.acc = a
            PROVE  SQ(BQ) = Q1b(BQ)
        <5>1. ASSUME NEW m ∈ P!sentMsgs("1b", b),
                         m.acc ∈ Q(BQ)
                     PROVE m ∈ SQ(BQ)
          BY <4>2, <4>3, <5>1, MsgsTypeLemma
             DEF P!sentMsgs, msgs, 1bmsgs, acceptorMsgsOfType, msgsOfType,
                 1bRestrict, InvP, Inv, knowsSentInv, 1bInv2
        <5>2. ASSUME NEW m ∈ SS,
                     m.acc ∈ Q(BQ)
              PROVE  1bRestrict(m) ∈ Q1b(BQ)
          BY <4>2, <5>2
             DEF InvP, Inv, knowsSentInv, msgsOfType, acceptorMsgsOfType, msgs,
                 1bmsgs, P!sentMsgs, 1bRestrict
        <5>3. QED
          BY <5>1, <5>2 DEF Q1b, SQ
      <4>4. CASE KnowsSafeAt(ac, b, v)!1!1'
        <5>1. PICK BQ ∈ ByzQuorum : KnowsSafeAt(ac, b, v)!1!1!(BQ)'
          BY <4>4
        <5>2. ∀ a ∈ Q(BQ) : ∃ m ∈ SQ(BQ) : ∧ m.acc = a
                                           ∧ m.mbal = -1
          BY <5>1, Isa DEF 1bRestrict
        <5>3. ∀ m ∈ SQ(BQ) : m.mbal = -1
          BY <4>2, <5>2
             DEF InvP, Inv, knowsSentInv, msgsOfType, 1bRestrict, 1bInv2
        <5>4. SQ(BQ) = Q1b(BQ)
          BY  <4>3, <5>1
        <5>5. Q(BQ) ∈ Quorum
          BY DEF Quorum
        <5> HIDE DEF SS, Q, SQ
        <5> WITNESS Q(BQ) ∈ Quorum
        <5>6. QED
          BY <5>2, <5>3, <5>4 DEF P!ShowsSafeAt
      <4>5. CASE KnowsSafeAt(ac, b, v)!1!2'
        <5>1. PICK c ∈ 0‥(b-1) : KnowsSafeAt(ac, b, v)!1!2!(c)'
          BY <4>5
        <5>2. PICK BQ ∈ ByzQuorum :
                      ∀ a ∈ BQ : ∃ m ∈ SS : ∧ m.acc = a
                                            ∧ m.mbal ≤ c
                                            ∧ (m.mbal = c) ⇒ (m.mval = v)
          BY <5>1
        <5>3. SQ(BQ) = Q1b(BQ)
          BY <5>2, <4>3
        <5>4. P!ShowsSafeAt(Q(BQ), b, v)!1!1
          <6>1. SUFFICES ASSUME NEW a ∈ Q(BQ)
                         PROVE ∃ m ∈ Q1b(BQ) : m.acc = a
            OBVIOUS
          <6>2. PICK m ∈ SS : m.acc = a
            BY <5>2
          <6>3. ∧ 1bRestrict(m) ∈ SQ(BQ)
                ∧ 1bRestrict(m).acc = a
            BY <6>2 DEF 1bRestrict
          <6>. QED
            BY <6>3, <5>3
        <5>5. PICK m1c ∈ msgs :
                  ∧ m1c = [type ↦ "1c", bal ↦ m1c.bal, val ↦ v]
                  ∧ m1c.bal ≥ c
                  ∧ m1c.bal ∈ Ballot
          <6>1. PICK WQ ∈ WeakQuorum :
                  ∀ a ∈ WQ : ∃ m ∈ SS : ∧ m.acc = a
                                        ∧ ∃ r ∈ m.m2av :
                                                      ∧ r.bal ≥ c
                                                      ∧ r.val = v
            BY <5>1
          <6>2. PICK a ∈ WQ, m ∈ SS :
                          ∧ a ∈ Acceptor
                          ∧ m.acc = a
                          ∧ ∃ r ∈ m.m2av : ∧ r.bal ≥ c
                                           ∧ r.val = v
            BY <6>1, BQA
          <6>4. PICK r ∈ m.m2av : ∧ r.bal ≥ c
                                  ∧ r.val = v
             BY <6>2
          <6>5. ∧ m.bal = b
                ∧ m ∈ bmsgs
                ∧ m.type = "1b"
                ∧ r.bal ∈ Ballot
            BY <4>2, <6>2, BMessageLemma
               DEF Inv, InvP, TypeOK, 1bMessage, knowsSentInv, msgsOfType
          <6>. QED
            BY <6>2, <6>4, <6>5, Zenon DEF Inv, 1bInv1
        <5>6. ASSUME NEW m ∈ Q1b(BQ)
              PROVE  ∧ m1c.bal ≥ m.mbal
                     ∧ (m1c.bal = m.mbal) ⇒ (m.mval = v)
          <6>1. PICK mm ∈ SS : ∧ mm.acc = m.acc
                               ∧ mm.mbal ≤ c
                               ∧ (mm.mbal = c) ⇒ (mm.mval = v)
            BY <5>2
          <6>2. PICK mm2 ∈ SS : ∧ mm2.acc = m.acc
                                ∧ m = 1bRestrict(mm2)
            BY <5>3 DEF 1bRestrict
          <6>3. ∧ mm = mm2
                ∧ mm2.mbal ∈ Ballot ∪ {-1}
            BY <4>2, <6>1, <6>2, BMessageLemma
               DEF Inv, InvP, TypeOK, knowsSentInv, 1bInv2, msgsOfType, 1bMessage
          <6>. QED
            <7> ∀ m1cbal, mmbal ∈ Ballot ∪ {-1} :
                    mmbal ≤ c ∧ m1cbal ≥ c ⇒ ∧ m1cbal ≥ mmbal
                                             ∧ mmbal = m1cbal ⇒ mmbal = c
              BY DEF Ballot
            <7> QED
              BY <5>5, <6>1, <6>2, <6>3 DEF 1bRestrict
        <5>7. P!ShowsSafeAt(Q(BQ), b, v)!1!2!2!(m1c)
          BY <5>5, <5>6
        <5>. QED
          BY <5>4, <5>7, Isa DEF P!ShowsSafeAt, Quorum
      <4>6. QED
        BY <3>1, <4>1, <4>4, <4>5 DEF KnowsSafeAt
    <3>6. QED
      BY <2>6, <3>1, <3>2, <3>3, <3>4, Zenon
         DEF LearnsSent, P!Phase1c, P!TLANext, Ballot, P!Ballot, PmaxBal, 1bOr2bMsgs
  <2>7. ASSUME NEW self ∈ Ballot,
               Phase1a(self)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. msgs' = msgs ∪ {[type ↦ "1a", bal ↦ self]}
      BY <2>7, MsgsLemma DEF Inv
    <3>2. UNCHANGED ⟨ PmaxBal, maxVBal, maxVVal ⟩
      BY <2>7, Isa DEF Phase1a, PmaxBal, 1bOr2bMsgs
    <3>. QED
      BY <3>1, <3>2 DEF P!Phase1a, P!TLANext, Ballot, P!Ballot
  <2>8. ASSUME NEW self ∈ Ballot,
               Phase1c(self)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. PICK SS ∈ SUBSET [type : {"1c"}, bal : {self}, val : Value] :
                ∧ ∀ m ∈ SS : ∃ a ∈ Acceptor : KnowsSafeAt(a, m.bal, m.val)
                ∧ msgs' = msgs ∪ SS
      BY <2>8, MsgsLemma DEF Inv
    <3> DEFINE S ≜ {m.val : m ∈ SS}
    <3>2. SS = {[type ↦ "1c", bal ↦ self, val ↦ v] : v ∈ S}
      OBVIOUS
    <3>3. ASSUME NEW v ∈ S
          PROVE  ∃ Q ∈ Quorum : P!ShowsSafeAt(Q, self, v)
      <4> DEFINE m ≜ [type ↦ "1c", bal ↦ self, val ↦ v]
      <4>1. PICK a ∈ Acceptor : KnowsSafeAt(a, self, v)
        BY <3>1
      <4> DEFINE SK ≜ {mm ∈ knowsSent[a] : mm.bal = self}
      <4>2. ASSUME NEW BQ ∈ ByzQuorum,
                       ∀ ac ∈ BQ : ∃ mm ∈ SK : mm.acc = ac
             PROVE  P!ShowsSafeAt(BQ ∩ Acceptor, self, v)!1!1
        <5> DEFINE Q ≜ BQ ∩ Acceptor
                   Q1b ≜ {mm ∈ P!sentMsgs("1b", self) : mm.acc ∈ Q}
        <5> SUFFICES ASSUME NEW ac ∈ BQ ∩ Acceptor
                     PROVE  ∃ mm ∈ Q1b : mm.acc = ac
          OBVIOUS
        <5>1. PICK mm ∈ SK : mm.acc = ac
          BY <4>2
        <5>2. ∧ 1bRestrict(mm) ∈ P!sentMsgs("1b", self)
              ∧ 1bRestrict(mm).acc = ac
          BY <5>1 DEF acceptorMsgsOfType, msgsOfType, 1bmsgs, msgs, Inv, knowsSentInv,
                      1bRestrict, P!sentMsgs
        <5>. QED
          BY <5>2
      <4>3. CASE KnowsSafeAt(a, self, v)!1!1
        <5>1. PICK BQ ∈ ByzQuorum :
                     ∀ ac ∈ BQ : ∃ mm ∈ SK : ∧ mm.acc = ac
                                             ∧ mm.mbal = -1
          BY <4>3
        <5> DEFINE Q ≜ BQ ∩ Acceptor
                   Q1b ≜ {mm ∈ P!sentMsgs("1b", self) : mm.acc ∈ Q}
        <5>2. P!ShowsSafeAt(Q, self, v)!1!1
          BY <5>1, <4>2
        <5>3. ASSUME NEW mm ∈ Q1b
              PROVE  mm.mbal = -1
          BY <5>1, MsgsTypeLemma
             DEF P!sentMsgs, 1bmsgs, acceptorMsgsOfType, msgsOfType, 1bRestrict,
                 Inv, knowsSentInv, 1bInv2, 1bRestrict
        <5>. QED
          BY <5>2, <5>3, Zenon DEF P!ShowsSafeAt, Quorum
      <4>4. CASE KnowsSafeAt(a, self, v)!1!2
        <5>1. PICK c ∈ 0‥(self-1) : KnowsSafeAt(a, self, v)!1!2!(c)
          BY <4>4
        <5>2. PICK BQ ∈ ByzQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!1!(BQ)
          BY <5>1
        <5> DEFINE Q ≜ BQ ∩ Acceptor
                   Q1b ≜ {mm ∈ P!sentMsgs("1b", self) : mm.acc ∈ Q}
        <5>3. P!ShowsSafeAt(Q, self, v)!1!1
          BY <5>2, <4>2
        <5>4. PICK WQ ∈ WeakQuorum : KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)
          BY <5>1
        <5>5. PICK ac ∈ WQ ∩ Acceptor :
                KnowsSafeAt(a, self, v)!1!2!(c)!2!(WQ)!(ac)
          BY <5>4, BQA
        <5>6. PICK mk ∈ SK : ∧ mk.acc = ac
                             ∧ ∃ r ∈ mk.m2av : ∧ r.bal ≥ c
                                               ∧ r.val = v
          BY <5>5
        <5>7. PICK r ∈ mk.m2av : ∧ r.bal ≥ c
                                    ∧ r.val = v
          BY <5>6
        <5> DEFINE mc ≜ [type ↦ "1c", bal ↦ r.bal, val ↦ v]
        <5>9. mc ∈ msgs
          BY <5>6, <5>7 DEF Inv, 1bInv1, knowsSentInv, msgsOfType
        <5>10. ASSUME NEW mq ∈  Q1b
               PROVE  ∧ mc.bal ≥ mq.mbal
                      ∧ (mc.bal = mq.mbal) ⇒ (mq.mval = v)
          BY <5>2, <5>7, MsgsTypeLemma, BMessageLemma
             DEF P!sentMsgs, 1bmsgs, acceptorMsgsOfType, msgsOfType, 1bRestrict,
                 Inv, TypeOK, 1bInv2, knowsSentInv, 1bMessage, Ballot
        <5>11. QED
          <6> Q ∈ Quorum
            BY DEF Quorum
          <6> WITNESS Q ∈ Quorum
          <6> QED
            BY <5>3, <5>9, <5>10 DEF P!ShowsSafeAt
      <4>5. QED
        BY <4>1, <4>3, <4>4 DEF KnowsSafeAt
    <3>. QED
      BY <2>8, <3>1, <3>2, <3>3, Zenon
         DEF P!Phase1c, Phase1c, PmaxBal, 1bOr2bMsgs, P!TLANext, Ballot, P!Ballot
  <2>9. ASSUME NEW self ∈ FakeAcceptor,
               FakingAcceptor(self)
        PROVE  P!TLANext ∨ P!vars' = P!vars
    <3>1. msgs' = msgs
      BY <2>9, MsgsLemma DEF Inv
    <3>2. PmaxBal' = PmaxBal
      BY <2>9, BQA, Zenon DEF FakingAcceptor, PmaxBal, 1bOr2bMsgs
    <3>. QED
      BY <2>9, <3>1, <3>2 DEF P!vars, FakingAcceptor
  <2>10. QED
    BY  <2>3,  <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, NextDef

<1>3. QED
  BY <1>1, <1>2, Invariance, PTL DEF Spec, P!Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* To see how learning is implemented, we must describe how to determine   *)
(* that a value has been chosen.  This is done by the following definition *)
(* of `chosen' to be the set of chosen values.                             *)
(***************************************************************************)
chosen ≜ {v ∈ Value : ∃ BQ ∈ ByzQuorum, b ∈ Ballot :
                           ∀ a ∈ BQ : ∃ m ∈ msgs : ∧ m.type = "2b"
                                                   ∧ m.acc  = a
                                                   ∧ m.bal  = b
                                                   ∧ m.val  = v}
(***************************************************************************)
(* The correctness of our definition of `chosen' is expressed by the       *)
(* following theorem, which asserts that if a value is in `chosen', then   *)
(* it is also in the set `chosen' of the emulated execution of the         *)
(* PCon algorithm.                                                         *)
(*                                                                         *)
(* The state function `chosen' does not necessarily equal the              *)
(* corresponding state function of the PCon algorithm.  It                 *)
(* requires every (real or fake) acceptor in a ByzQuorum to vote for (send *)
(* 2b messages) for a value v in the same ballot for v to be in `chosen'   *)
(* for the BPCon algorithm, but it requires only that every (real)         *)
(* acceptor in a Quorum vote for v in the same ballot for v to be in the   *)
(* set `chosen' of the emulated execution of algorithm PCon.               *)
(*                                                                         *)
(* Liveness for BPCon requires that, under suitable assumptions, some      *)
(* value is eventually in `chosen'.  Since we can't assume that a fake     *)
(* acceptor does anything useful, liveness requires the assumption that    *)
(* there is a ByzQuorum composed entirely of real acceptors (the first     *)
(* conjunct of assumption BQLA).                                           *)
(***************************************************************************)
THEOREM chosen ⊆ P!chosen
BY Isa DEF chosen, P!chosen, Quorum, Ballot, P!Ballot

==============================================================================
\* Modification History
\* Last modified Sat Jul 25 17:34:50 PDT 2020 by lamport
\* Last modified Fri Jul 24 17:51:34 CEST 2020 by merz
\* Last modified Wed Apr 15 15:16:26 CEST 2020 by doligez
\* Last modified Mon Aug 18 14:57:27 CEST 2014 by tomer
\* Last modified Mon Mar 04 17:24:05 CET 2013 by doligez
\* Last modified Wed Dec 01 11:35:29 PST 2010 by lamport