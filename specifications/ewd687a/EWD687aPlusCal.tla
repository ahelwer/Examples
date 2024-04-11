-------------------------- MODULE EWD687aPlusCal --------------------------
(***************************************************************************)
(* PlusCal representation of the algorithm by Dijkstra and Scholten for    *)
(* detecting the termination of a distributed computation initiated by a   *)
(* designated root node. The algorithm maintains a spanning tree that      *)
(* contains all active nodes. Inactive leaf nodes detach themselves from   *)
(* the tree, but note that a node may later be reactivated by receiving    *)
(* a message and may reattach itself to the tree. When the root node has   *)
(* no more children and becomes inactive, it declares termination.         *)
(*                                                                         *)
(* E.W. Dijkstra, C.S. Scholten: Termination detection for diffusing       *)
(* computations. Information Processing Letters, 11 (1):1–4, 1980.         *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

CONSTANT 
  Node,        \* the set of active nodes
  initiator,   \* initiator node
  maxMsg       \* maximum number of pending messages for bounding the state space

ASSUME ∧ IsFiniteSet(Node)
       ∧ initiator ∈ Node

none ≜ CHOOSE x : x ∉ Node

(* 
--algorithm DS {
  variable
    (* has termination been detected? *)
    terminationDetected = FALSE,
    (* For every node we keep the following counters:
       - number of base messages received, per sending node
       - number of ack messages received *)
    network = [n ∈ Node ↦ [msg ↦ [snd ∈ Node ↦ 0], ack ↦ 0]];
  define {
    (* operators for sending and receiving messages:
       the result is the network resulting from the operation *)
    sendMsg(net, from, to) ≜ [net EXCEPT ![to].msg[from] = @+1]
    pendingMsg(net, to, from) ≜ net[to].msg[from] > 0
    receiveMsg(net, to, from) ≜ [net EXCEPT ![to].msg[from] = @-1]
    sendAck(net, to) ≜ [net EXCEPT ![to].ack = @+1]
    pendingAck(net, to) ≜ net[to].ack > 0
    receiveAck(net, to) ≜ [net EXCEPT ![to].ack = @-1]
  }
  fair process (node ∈ Node) 
    variables active = (self = initiator),
              parent = IF self = initiator THEN self ELSE none,
              activeSons = 0;
  {
l:  while (TRUE) {
      either { \* send a (base) message to some other node
        when active;
        with (dst ∈ Node \ {self}) {
          network ≔ sendMsg(network, self, dst)
        };
        activeSons ≔ activeSons + 1
      } or { \* terminate
        when active;
        active ≔ FALSE
      } or { \* receive a base message
        with (snd ∈ Node) {
          when pendingMsg(network, self, snd);
          active ≔ TRUE;
          with (net = receiveMsg(network, self, snd)) {
            \* accept sender as parent if there is none, else send ack
            if (parent = none) {
               parent ≔ snd;
               network ≔ net
            } else {
               network ≔ sendAck(net, snd)
            }
          }
        }
      } or { \* receive an ack
        when pendingAck(network, self);
        network ≔ receiveAck(network, self);
        activeSons ≔ activeSons - 1
      } or { \* detach or declare termination
        when (¬active ∧ activeSons = 0 ∧ parent ≠ none);
        if (parent = self) {
           terminationDetected ≔ TRUE
        } else {
          network ≔ sendAck(network, parent);
        };
        parent ≔ none
      }
    }
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "d18d3150" /\ chksum(tla) = "7d13cf45")
VARIABLES terminationDetected, network

(* define statement *)
sendMsg(net, from, to) ≜ [net EXCEPT ![to].msg[from] = @+1]
pendingMsg(net, to, from) ≜ net[to].msg[from] > 0
receiveMsg(net, to, from) ≜ [net EXCEPT ![to].msg[from] = @-1]
sendAck(net, to) ≜ [net EXCEPT ![to].ack = @+1]
pendingAck(net, to) ≜ net[to].ack > 0
receiveAck(net, to) ≜ [net EXCEPT ![to].ack = @-1]

VARIABLES active, parent, activeSons

vars ≜ ⟨ terminationDetected, network, active, parent, activeSons ⟩

ProcSet ≜ (Node)

Init ≜ (* Global variables *)
        ∧ terminationDetected = FALSE
        ∧ network = [n ∈ Node ↦ [msg ↦ [snd ∈ Node ↦ 0], ack ↦ 0]]
        (* Process node *)
        ∧ active = [self ∈ Node ↦ (self = initiator)]
        ∧ parent = [self ∈ Node ↦ IF self = initiator THEN self ELSE none]
        ∧ activeSons = [self ∈ Node ↦ 0]

node(self) ≜ ∨ ∧ active[self]
               ∧ ∃ dst ∈ Node \ {self}:
                      network' = sendMsg(network, self, dst)
               ∧ activeSons' = [activeSons EXCEPT ![self] = activeSons[self] + 1]
               ∧ UNCHANGED ⟨terminationDetected, active, parent⟩
             ∨ ∧ active[self]
               ∧ active' = [active EXCEPT ![self] = FALSE]
               ∧ UNCHANGED ⟨terminationDetected, network, parent, activeSons⟩
             ∨ ∧ ∃ snd ∈ Node:
                      ∧ pendingMsg(network, self, snd)
                      ∧ active' = [active EXCEPT ![self] = TRUE]
                      ∧ LET net ≜ receiveMsg(network, self, snd) IN
                           IF parent[self] = none
                              THEN ∧ parent' = [parent EXCEPT ![self] = snd]
                                   ∧ network' = net
                              ELSE ∧ network' = sendAck(net, snd)
                                   ∧ UNCHANGED parent
               ∧ UNCHANGED ⟨terminationDetected, activeSons⟩
             ∨ ∧ pendingAck(network, self)
               ∧ network' = receiveAck(network, self)
               ∧ activeSons' = [activeSons EXCEPT ![self] = activeSons[self] - 1]
               ∧ UNCHANGED ⟨terminationDetected, active, parent⟩
             ∨ ∧ (¬active[self] ∧ activeSons[self] = 0 ∧ parent[self] ≠ none)
               ∧ IF parent[self] = self
                       THEN ∧ terminationDetected' = TRUE
                            ∧ UNCHANGED network
                       ELSE ∧ network' = sendAck(network, parent[self])
                            ∧ UNCHANGED terminationDetected
               ∧ parent' = [parent EXCEPT ![self] = none]
               ∧ UNCHANGED ⟨active, activeSons⟩

Next ≜ (∃ self ∈ Node: node(self))

Spec ≜ ∧ Init ∧ □[Next]_vars
       ∧ ∀ self ∈ Node : WF_vars(node(self))

\* END TRANSLATION 

StateConstraint ≜
  ∧ ∀ n ∈ Node : network[n].ack ≤ 2 
  ∧ ∀ m,n ∈ Node : network[m].msg[n] ≤ maxMsg

TypeOK ≜
  ∧ terminationDetected ∈ BOOLEAN
  ∧ network ∈ [Node → [msg : [Node → ℕ], ack : ℕ]]
  ∧ active ∈ [Node → BOOLEAN]
  ∧ parent ∈ [Node → Node ∪ {none}]
  ∧ activeSons ∈ [Node → ℕ]

Quiescence ≜
  ∧ ∀ n ∈ Node : ¬active[n]
  ∧ ∀ n ∈ Node : network[n].ack = 0
  ∧ ∀ m,n ∈ Node : network[n].msg[m] = 0

(***************************************************************************)
(* The main safety property requires that termination is detected only     *)
(* when the system is indeed quiescent.                                    *)
(***************************************************************************)
TerminationDetection ≜ terminationDetected ⇒ Quiescence

(***************************************************************************)
(* Conversely, liveness requires that if the system becomes quiescent      *)
(* (which is not guaranteed) then termination is eventually detected.      *)
(***************************************************************************)
Liveness ≜ Quiescence ↝ terminationDetected

=============================================================================
\* Modification History
\* Last modified Tue Feb 09 17:33:02 CET 2021 by merz
\* Created Tue Feb 09 11:32:36 CET 2021 by merz