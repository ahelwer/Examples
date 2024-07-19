------------------------------ MODULE Network -------------------------------
(***************************************************************************)
(* NETWORKING OPERATIONS                                                   *)
(*                                                                         *)
(* Various network-related operations (send & receiving messages, etc.)    *)
(* and their adaptations for sequential vs. unordered messaging models.    *)
(*                                                                         *)
(***************************************************************************)

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

CONSTANTS
  Node,
  Message,
  Ordered,
  Duplicates,
  Loss

ASSUME
  ∧ Node ≠ {}
  ∧ Message ≠ {}
  ∧ Ordered ∈ BOOLEAN
  ∧ Duplicates ∈ BOOLEAN
  ∧ Loss ∈ BOOLEAN

\* Converts a sequence into an unordered set of unique elements
SeqToSet(seq) ≜ {seq[i] : i ∈ 1 ‥ Len(seq)}

\* Transforms every element of a sequence with some operator
MapSeq(seq, f(_)) ≜ [i ∈ 1 ‥ Len(seq) ↦ f(seq[i])]

\* The set of all possible pending messages; useful for type invariants
PendingMessage ≜
  IF Ordered
  THEN [Node → Seq(Message)]
  ELSE SUBSET Message

\* The set of messages currently pending at a node
CurrentlyPendingMessages(pending) ≜
  IF Ordered
  THEN UNION {SeqToSet(pending[n]) : n ∈ Node}
  ELSE pending

\* Transforms all pending messages with some operator
MapPendingMessages(pending, f(_)) ≜
  IF Ordered
  THEN [n ∈ Node ↦ MapSeq(pending[n], f)]
  ELSE {f(msg) : msg ∈ pending}

\* The state of having no pending messages; useful for initial states
NoPendingMessages ≜
  IF Ordered
  THEN [n ∈ Node ↦ ⟨⟩]
  ELSE {}

\* Add a message to the pending messages at the recipient node
SendMessage(pending, sender, success, msg) ≜
  IF Loss ∧ ¬success
  THEN pending
  ELSE IF Ordered
    THEN [pending EXCEPT ![sender] = Append(@, msg)]
    ELSE pending ∪ {msg}

\* Get the next message to be received
PeekMessage(pending) ≜
  IF Ordered
  THEN {Head(pending[n]) : n ∈ {n ∈ Node : pending[n] ≠ ⟨⟩}}
  ELSE pending

\* Mark a message as having been received
ReceiveMessage(pending, sender, duplicate, msg) ≜
  IF Duplicates ∧ duplicate
  THEN pending
  ELSE IF Ordered
    THEN [pending EXCEPT ![sender] = Tail(@)]
    ELSE pending \ {msg}

\* Re-enqueue a message to be processed at a later time
ReEnqueueMessage(pending, sender, msg) ≜
  IF Ordered
  THEN [pending EXCEPT ![sender] = Append(Tail(@), msg)]
  ELSE pending

=============================================================================

