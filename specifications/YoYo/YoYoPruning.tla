------------------------------ MODULE YoYoPruning ----------------------------
(****************************************************************************)
(* The version of the Yo-Yo algorithm without pruning stabilizes in a state *)
(* with a single source node. However, that algorithm does not terminate,   *)
(* and no single node can detect that the algorithm has stabilized. In      *)
(* order to ensure termination, the "up" ("-Yo") phase of the algorithm is  *)
(* extended in order to prune the graph by applying the following rules.    *)
(*                                                                          *)
(* 1. A sink node with a single (incoming) neighbor receives only one value *)
(*    during the "down" phase, and therefore replies "yes" in the "up"      *)
(*    phase of the algorithm. Since it does not contribute any useful       *)
(*    information, it will become inactive and be removed from the graph.   *)
(* 2. A node (internal or sink) that receives the same value from several   *)
(*    neighbors non-deterministically chooses one of these neighbors and    *)
(*    prunes the links to all other neighbors that sent the same value.     *)
(*    The rationale is that these neighbors correspond to different paths   *)
(*    from the same source node, and maintaining one path is enough.        *)
(*                                                                          *)
(* Applying these two rules, nodes and links are eliminated until the only  *)
(* remaining source becomes an isolated node, at which point it proclaims   *)
(* itself to be the leader. All other nodes will have become inactive.      *)
(* The pruning phase is implemented by adding a flag to "up" messages,      *)
(* indicating to the receiver whether to prune the corresponding link.      *)
(*                                                                          *)
(* Authors: Ludovic Yvoz and Stephan Merz, 2024.                            *)
(****************************************************************************)

EXTENDS TLC, Integers, FiniteSets, UndirectedGraphs

CONSTANT Nodes, Edges   \* the nodes and edges of the graph

ASSUME  
  (* nodes are represented by their integer identities *)
  ∧ Nodes ⊆ ℤ
  ∧ Nodes ≠ {} 
  ∧ LET G ≜ [node ↦ Nodes, edge ↦ Edges]
     IN  ∧ IsUndirectedGraph(G)
         ∧ IsStronglyConnected(G)

Neighbors(n) ≜ {m ∈ Nodes : {m,n} ∈ Edges}

Min(S) ≜ CHOOSE x ∈ S : ∀ y ∈ S : x ≤ y

VARIABLES 
  (* the activation status of the node *)
  active,
  (* the phase (down or up) each node is currently executing *)
  phase,
  (* incoming and outgoing neighbors of each node *)
  incoming, outgoing,
  (* mailbox of each node *)
  mailbox

vars ≜ ⟨active, phase, incoming, outgoing, mailbox⟩

(****************************************************************************)
(* Determine the kind of the node: leader, source, sink or internal.        *)
(****************************************************************************)
kind(n) ≜
    IF incoming[n] = {} ∧ outgoing[n] = {} THEN "leader"
    ELSE IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

(****************************************************************************)
(* Messages sent during the algorithm.                                      *)
(****************************************************************************)
Messages ≜ 
  [phase : {"down"}, sndr : Nodes, val : Nodes] ∪  
  [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
downMsg(s,v) ≜ [phase ↦ "down", sndr ↦ s, val ↦ v]
upMsg(s,r,p) ≜ [phase ↦ "up", sndr ↦ s, reply ↦ r, prune ↦ p]

(****************************************************************************)
(* Type correctness predicate.                                              *)
(****************************************************************************)
TypeOK ≜ 
    ∧ active ∈ [Nodes → BOOLEAN]
    ∧ phase ∈ [Nodes → {"down", "up"}]
    ∧ incoming ∈ [Nodes → SUBSET Nodes]
    ∧ ∀ n ∈ Nodes : incoming[n] ⊆ Neighbors(n)
    ∧ outgoing ∈ [Nodes → SUBSET Nodes]
    ∧ ∀ n ∈ Nodes : outgoing[n] ⊆ Neighbors(n)
    ∧ mailbox ∈ [Nodes → SUBSET Messages]
    ∧ ∀ n ∈ Nodes : ∀ msg ∈ mailbox[n] :
          ∧ msg.phase = "down" ⇒ 
             ∧ n ∈ outgoing[msg.sndr]
             ∧ ∀ mm ∈ mailbox[n] : \* at most one message per neighbor
                   mm.phase = "down" ∧ mm.sndr = msg.sndr ⇒ mm = msg
          ∧ msg.phase = "up" ⇒ 
             ∧ msg.sndr ∈ outgoing[n]
             ∧ ∀ mm ∈ mailbox[n] : \* at most one message per neighbor
                   mm.phase = "up" ∧ mm.sndr = msg.sndr ⇒ mm = msg

------------------------------------------------------------------------------
(****************************************************************************)
(* Yo-Yo algorithm as a state machine.                                      *)
(****************************************************************************)
Init ≜ 
    ∧ active = [n ∈ Nodes ↦ TRUE]
    ∧ phase = [n ∈ Nodes ↦ "down"]
    ∧ incoming = [n ∈ Nodes ↦ { m ∈ Neighbors(n) : m < n}]
    ∧ outgoing = [n ∈ Nodes ↦ { m ∈ Neighbors(n) : m > n}]
    ∧ mailbox = [n ∈ Nodes ↦ {}]

------------------------------------------------------------------------------
(****************************************************************************)
(* Down phase: we distinguish sources and other nodes.                      *)
(* Note that a node retains "down" messages after executing the phase       *)
(* because they are used during the up phase.                               *)
(****************************************************************************)
DownSource(n) ≜ 
    ∧ active[n]
    ∧ kind(n) = "source"
    ∧ phase[n] = "down"
    ∧ mailbox' = [m ∈ Nodes ↦ 
        IF m ∈ outgoing[n] THEN mailbox[m] ∪ {downMsg(n,n)}
        ELSE mailbox[m]]
    ∧ phase' = [phase EXCEPT ![n] = "up"]
    ∧ UNCHANGED ⟨active, incoming, outgoing⟩

DownOther(n) ≜ 
    ∧ active[n]
    ∧ kind(n) ∈ {"internal", "sink"}
    ∧ phase[n] = "down"
    ∧ LET downMsgs ≜ {msg ∈ mailbox[n] : msg.phase = "down"}
       IN  ∧ {msg.sndr : msg ∈ downMsgs} = incoming[n]
           ∧ LET min ≜ Min({msg.val : msg ∈ downMsgs})
              IN mailbox' = [m ∈ Nodes ↦
                             IF m ∈ outgoing[n] 
                             THEN mailbox[m] ∪ {downMsg(n,min)}
                             ELSE mailbox[m]]
    ∧ phase' = [phase EXCEPT ![n] = "up"]
    ∧ UNCHANGED ⟨active, incoming, outgoing⟩

Down(n) ≜ DownSource(n) ∨ DownOther(n)

------------------------------------------------------------------------------
(****************************************************************************)
(* Up phase, again distinguishing sources and other nodes.                  *)
(*                                                                          *)
(* An internal or source node may already have received "down" messages     *)
(* for the following round from neighbors that it still considers as        *)
(* outgoing neighbors but for which the edge direction was reversed.        *)
(* We therefore have to be careful to only consider "down" messages from    *)
(* neighbors that the node considers as incoming, and also to preserve      *)
(* "down" messages for the following round when cleaning the mailbox.       *)
(****************************************************************************)
UpSource(n) ≜
    ∧ active[n]
    ∧ kind(n) = "source"
    ∧ phase[n] = "up"
    ∧ LET upMsgs ≜ {msg ∈ mailbox[n] : msg.phase = "up"}
           noSndrs ≜ {msg.sndr : msg ∈ {mm ∈ upMsgs : mm.reply = "no"}}
           pruned ≜ {msg.sndr : msg ∈ {mm ∈ upMsgs : mm.prune}}
       IN  ∧ {msg.sndr : msg ∈ upMsgs} = outgoing[n]
           ∧ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
           ∧ incoming' = [incoming EXCEPT ![n] = noSndrs \ pruned]
           ∧ outgoing' = [outgoing EXCEPT ![n] = @ \ (noSndrs ∪ pruned)]
    ∧ phase' = [phase EXCEPT ![n] = "down"]
    ∧ active' = active

UpOther(n) ≜
    ∧ active[n]
    ∧ kind(n) ∈ {"internal", "sink"}
    ∧ phase[n] = "up"
    ∧ LET upMsgs ≜ {msg ∈ mailbox[n] : msg.phase = "up"}
           noSndrs ≜ {msg.sndr : msg ∈ {mm ∈ upMsgs : mm.reply = "no"}}
           pruned ≜ {msg.sndr : msg ∈ {mm ∈ upMsgs : mm.prune}}
           downMsgs ≜ {msg ∈ mailbox[n] : msg.phase = "down" ∧ msg.sndr ∈ incoming[n]}
           valsRcvd ≜ {msg.val : msg ∈ downMsgs}
           senders(v) ≜ {m ∈ incoming[n] : downMsg(m,v) ∈ downMsgs}
           valSent(m) ≜ (CHOOSE msg ∈ downMsgs : msg.sndr = m).val
           isLoneSink ≜ kind(n) = "sink" ∧ Cardinality(incoming[n]) = 1
       IN  ∧ {msg.sndr : msg ∈ upMsgs} = outgoing[n]  \* always true for sinks
           ∧ \* non-deterministically choose a sender for each value whose link
              \* will not be pruned
              ∃ keep ∈ {f ∈ [valsRcvd → incoming[n]] :
                             ∀ v ∈ valsRcvd : f[v] ∈ senders(v)} :
                 ∧ IF noSndrs = {}  \* true in particular for sinks
                    THEN LET min ≜ Min({msg.val : msg ∈ downMsgs})
                             minSndrs ≜ {msg.sndr : msg ∈ {mm ∈ downMsgs : mm.val = min}}
                         IN  ∧ mailbox' = [m ∈ Nodes ↦
                                  IF m ∈ incoming[n]
                                  THEN mailbox[m] ∪ 
                                    {upMsg(n, 
                                           IF m ∈ minSndrs THEN "yes" ELSE "no",
                                           (m ≠ keep[valSent(m)]) ∨ isLoneSink)}
                                  ELSE IF m = n THEN mailbox[m] \ (upMsgs ∪ downMsgs)
                                  ELSE mailbox[m]]
                             ∧ incoming' = [incoming EXCEPT ![n] = 
                                                IF isLoneSink THEN {} ELSE {keep[min]}]
                             ∧ outgoing' = [outgoing EXCEPT ![n] = 
                                                (@ \ pruned) ∪ 
                                                {keep[v] : v ∈ valsRcvd \ {min}}]
                    ELSE ∧ mailbox' = [m ∈ Nodes ↦
                              IF m ∈ incoming[n] 
                              THEN mailbox[m] ∪ {upMsg(n, "no", m ≠ keep[valSent(m)])}
                              ELSE IF m = n THEN mailbox[m] \ (upMsgs ∪ downMsgs)
                              ELSE mailbox[m]]
                         ∧ incoming' = [incoming EXCEPT ![n] = noSndrs \ pruned]
                         ∧ outgoing' = [outgoing EXCEPT ![n] = 
                                            (@ \ (noSndrs ∪ pruned)) ∪
                                            {keep[v] : v ∈ valsRcvd}]
                 ∧ active' = [active EXCEPT ![n] = ¬ isLoneSink]
    ∧ phase' = [phase EXCEPT ![n] = "down"]

Up(n) ≜ UpSource(n) ∨ UpOther(n)

------------------------------------------------------------------------------

Next ≜ ∃ n ∈ Nodes : Down(n) ∨ Up(n)

Spec ≜ Init ∧ □[Next]_vars ∧ WF_vars(Next)

------------------------------------------------------------------------------
(****************************************************************************)
(* Formulas used for verification.                                          *)
(****************************************************************************)

(****************************************************************************)
(* Predicate asserting that there will always be at least two source nodes. *)
(* Checking this as an invariant produces an execution that shows that all  *)
(* sources except for the leader will be eliminated.                        *)
(****************************************************************************)
MoreThanOneSource ≜ ∃ s1, s2 ∈ Nodes :
    s1 ≠ s2 ∧ kind(s1) = "source" ∧ kind(s2) = "source"

(****************************************************************************)
(* Node m is an outgoing neighbor of node n iff n is an incoming neighbor   *)
(* of m, except if the edge is being reversed, in which case there is a     *)
(* "no" message in one of the mailboxes, or if the edge is being pruned,    *)
(* in which case there is a corresponding message pending at node n.        *)
(****************************************************************************)
NeighborInv ≜ ∀ m,n ∈ Nodes :
  m ∈ outgoing[n] ⇔ 
    ∨ n ∈ incoming[m]
    ∨ ∧ n ∈ outgoing[m] 
      ∧ ∨ upMsg(n, "no", FALSE) ∈ mailbox[m] 
        ∨ upMsg(m, "no", FALSE) ∈ mailbox[n]
    ∨ ∧ n ∉ (incoming[m] ∪ outgoing[m])
      ∧ ∃ r ∈ {"yes", "no"} : upMsg(m, r, TRUE) ∈ mailbox[n]

(****************************************************************************)
(* The base algorithm without pruning ensures that no new sources are       *)
(* generated during execution of the algorithm. Due to pruning, this        *)
(* property may fail for the full algorithm, and TLC finds a counter-       *)
(* example for the small example graph provided in the MC module (but the   *)
(* property happens to be true for the larger graph).                       *)
(****************************************************************************)
NoNewSource ≜ 
  □[∀ n ∈ Nodes : kind(n)' = "source" ⇒ kind(n) = "source"]_vars

(****************************************************************************)
(* Termination condition: the node with smallest identity is the leader,    *)
(* all other nodes are inactive, all mailboxes are empty.                   *)
(* Check that the algorithm will reach such a state, and that this is the   *)
(* only final (deadlock) state.                                             *)
(****************************************************************************)
Termination ≜ ∀ n ∈ Nodes :
    ∧ IF n = Min(Nodes) THEN kind(n) = "leader" ELSE ¬ active[n]
    ∧ mailbox[n] = {}

Liveness ≜ ◇Termination
FinishIffTerminated ≜ ¬(ENABLED Next) ⇔ Termination
==============================================================================