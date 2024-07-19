------------------------ MODULE ByzantineGenerals ---------------------------
CONSTANTS Generals

VARIABLES network, confirmations

Vars ≜ ⟨network, connection⟩

CommandMessageType ≜ "Command"
CommandMessage ≜ [
  type    : {CommandMessageType},
  sender  : Node
]

ConfirmMessageType ≜ "Confirm"
ConfirmMessage ≜ [
  type    : {ConfirmMessageType},
  sender  : Node
]

MessageType ≜ {CommandMessageType, ConfirmMessageType}
Message ≜ CommandMessage ∪ ConfirmMessage

INSTANCE Network WITH Ordered ← FALSE, Duplicates ← TRUE, Loss ← TRUE

TypeOK ≜
  ∧ network ∈ [Node → PendingMessage]
  ∧ connection ∈ [Node → SUBSET Node]

Termination ≜ ∀ src, dst ∈ Node : dst ∈ connection[src]

Liveness ≜ □◇Termination

SendSynMessage(src, dst) ≜
  ∧ dst ∉ connection[src]
  ∧ ∃ success ∈ BOOLEAN :
    network' = [
      network EXCEPT
        ![dst] = SendMessage(@, src, success, [
          type    ↦ SynMessageType,
          sender  ↦ src
        ])
      ]
  ∧ UNCHANGED connection

ProcessSynMessage(recipient, sender, msg, success) ≜
  ∧ msg.type = SynMessageType
  ∧ ∃ duplicate ∈ BOOLEAN :
    network' = [
      network EXCEPT
        ![recipient] = ReceiveMessage(@, sender, duplicate, msg),
        ![sender] = SendMessage(@, recipient, success, [
          type    ↦ AckMessageType,
          sender  ↦ recipient
        ])
      ]
  ∧ UNCHANGED connection

ProcessAckMessage(recipient, sender, msg) ≜
  ∧ msg.type = AckMessageType
  ∧ ∃ duplicate ∈ BOOLEAN :
    network' = [
      network EXCEPT
        ![recipient] = ReceiveMessage(@, sender, duplicate, msg)
      ]
  ∧ connection' = [connection EXCEPT ![recipient] = @ ∪ {sender}]

ProcessMessage(recipient, sender, message_type, success) ≜
  ∃ msg ∈ PeekMessage(network[recipient]) :
    ∧ msg.type = message_type
    ∧ msg.sender = sender
    ∧ ∨ ProcessSynMessage(recipient, sender, msg, success)
      ∨ ProcessAckMessage(recipient, sender, msg)

Terminate ≜
  ∧ Termination
  ∧ UNCHANGED ⟨network, connection⟩

Init ≜
  ∧ network = [n ∈ Node ↦ NoPendingMessages]
  ∧ connection = [n ∈ Node ↦ {}]

Next ≜
  ∨ ∃ src, dst ∈ Node : SendSynMessage(src, dst)
  ∨ ∃ recipient, sender ∈ Node :
    ∃ message_type ∈ MessageType :
      ∃ success ∈ BOOLEAN :
        ProcessMessage(recipient, sender, message_type, success)
  ∨ Terminate

Fairness ≜
  ∧ ∀ src, dst ∈ Node : WF_Vars(SendSynMessage(src, dst))
  ∧ ∀ recipient, sender ∈ Node :
    SF_Vars(ProcessMessage(recipient, sender, SynMessageType, TRUE))
  ∧ ∀ recipient, sender ∈ Node :
    ∀ success ∈ BOOLEAN :
      WF_Vars(ProcessMessage(recipient, sender, AckMessageType, success))

Spec ≜
  ∧ Init
  ∧ □[Next]_Vars
  ∧ Fairness

=============================================================================

