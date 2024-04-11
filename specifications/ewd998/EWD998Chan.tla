----------------------------- MODULE EWD998Chan -----------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* Contrary to EWD998, this variant models message channels as sequences.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Utils

CONSTANT N
ASSUME NAssumption ≜ N ∈ ℕ \ {0} \* At least one node.

Node ≜ 0 ‥ N-1
Color ≜ {"white", "black"}

VARIABLES 
 active,
 color,
 counter,
 inbox
  
vars ≜ ⟨active, color, counter, inbox⟩

TokenMsg ≜ [type : {"tok"}, q : ℤ, color : Color]
BasicMsg ≜ [type : {"pl"}]
Message ≜ TokenMsg ∪ BasicMsg

TypeOK ≜
  ∧ counter ∈ [Node → ℤ]
  ∧ active ∈ [Node → BOOLEAN]
  ∧ color ∈ [Node → Color]
  ∧ inbox ∈ [Node → Seq(Message)]
  \* There is always exactly one token (singleton-type).
  ∧ ∃ i ∈ Node : ∃ j ∈ 1‥Len(inbox[i]): inbox[i][j].type = "tok"
  ∧ ∀ i,j ∈ Node : ∀ k ∈ 1 ‥ Len(inbox[i]) : ∀ l ∈ 1 ‥ Len(inbox[j]) :
        inbox[i][k].type = "tok" ∧ inbox[j][l].type = "tok"
        ⇒ i = j ∧ k = l

------------------------------------------------------------------------------
 
Init ≜
  (* Rule 0 *)
  ∧ counter = [i ∈ Node ↦ 0] \* c properly initialized
\*   /\ inbox = [i \in Node |-> IF i = 0 
\*                              THEN << [type |-> "tok", q |-> 0, color |-> "black" ] >> 
\*                              ELSE <<>>] \* with empty channels.
\* The token may be at any node of the ring initially.
  ∧ inbox ∈ { f ∈ 
                    [ Node → {⟨⟩, ⟨[type ↦ "tok", q ↦ 0, color ↦ "black" ]⟩ } ] : 
                        Cardinality({ i ∈ DOMAIN f: f[i] ≠ ⟨⟩ }) = 1 }
  (* EWD840 *) 
  ∧ active ∈ [Node → BOOLEAN]
  ∧ color ∈ [Node → Color]

InitiateProbe ≜
  (* Rule 1 *)
  ∧ ∃ j ∈ 1‥Len(inbox[0]):
      \* Token is at node 0.
      ∧ inbox[0][j].type = "tok"
      ∧ \* Previous round inconsistent, if:
         ∨ inbox[0][j].color = "black"
         ∨ color[0] = "black"
         \* Implicit stated in EWD998 as c0 + q > 0 means that termination has not 
         \* been achieved: Initiate a probe if the token's color is white but the
         \* number of in-flight messages is not zero.
         ∨ counter[0] + inbox[0][j].q ≠ 0
      ∧ inbox' = [inbox EXCEPT ![N-1] = Append(@, 
           [type ↦ "tok", q ↦ 0,
             (* Rule 6 *)
             color ↦ "white"]), 
             ![0] = RemoveAt(@, j) ] \* consume token message from inbox[0]. 
  (* Rule 6 *)
  ∧ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  ∧ UNCHANGED ⟨active, counter⟩                            
  
PassToken(i) ≜
  (* Rule 2 *)
  ∧ ¬ active[i] \* If machine i is active, keep the token.
  ∧ ∃ j ∈ 1‥Len(inbox[i]) : 
          ∧ inbox[i][j].type = "tok"
          \* the machine nr.i+1 transmits the token to machine nr.i under q := q + c[i+1]
          ∧ LET tkn ≜ inbox[i][j]
             IN  inbox' = [inbox EXCEPT ![i-1] = 
                                       Append(@, [tkn EXCEPT !.q = tkn.q + counter[i],
                                                             !.color = IF color[i] = "black"
                                                                       THEN "black"
                                                                       ELSE tkn.color]),
                                    ![i] = RemoveAt(@, j) ] \* pass on the token.
  (* Rule 7 *)
  ∧ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  ∧ UNCHANGED ⟨active, counter⟩                            

System ≜ ∨ InitiateProbe
         ∨ ∃ i ∈ Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ≜
  \* Only allowed to send msgs if node i is active.
  ∧ active[i]
  (* Rule 0 *)
  ∧ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  ∧ ∃ j ∈ Node \ {i} :
          \* Send a message (not the token) to j.
          ∧ inbox' = [inbox EXCEPT ![j] = Append(@, [type ↦ "pl" ] ) ]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  ∧ UNCHANGED ⟨active, color⟩                            

RecvMsg(i) ≜
  (* Rule 0 *)
  ∧ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  ∧ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  ∧ active' = [ active EXCEPT ![i] = TRUE ]
  \* Consume a message (not the token!).
  ∧ ∃ j ∈ 1‥Len(inbox[i]) : 
          ∧ inbox[i][j].type = "pl"
          ∧ inbox' = [inbox EXCEPT ![i] = RemoveAt(@, j) ]
  ∧ UNCHANGED ⟨⟩                           

Deactivate(i) ≜
  ∧ active[i]
  ∧ active' = [active EXCEPT ![i] = FALSE]
  ∧ UNCHANGED ⟨color, inbox, counter⟩

Environment ≜ ∃ i ∈ Node : SendMsg(i) ∨ RecvMsg(i) ∨ Deactivate(i)

-----------------------------------------------------------------------------

Next ≜
  System ∨ Environment

Spec ≜ Init ∧ □[Next]_vars ∧ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* The number of incoming messages of a node's given inbox.                *)
(***************************************************************************)
NumberOfMsg(ibx) ≜ 
  Len(SelectSeq(ibx, LAMBDA msg: msg.type = "pl"))

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ≜
  ∧ ∀ i ∈ DOMAIN inbox : NumberOfMsg(inbox[i]) < 3
\*  /\ \A i \in DOMAIN inbox : Len(inbox[i]) < 3
  \* Even with the number of in-flight messages restricted, we need a bound
  \* on the number of messages ever sent to exclude behaviors where two or
  \* more nodes forever alternate between send, receive, send, ...
  ∧ ∀ i ∈ DOMAIN counter : counter[i] ≤ 3

-----------------------------------------------------------------------------

(***************************************************************************)
(* tpos \in Node s.t. the node's inbox contains the token.                *)
(***************************************************************************)
tpos ≜
  CHOOSE i ∈ Node : ∃ j ∈ 1‥Len(inbox[i]) : inbox[i][j].type = "tok"

token ≜
    LET idx ≜ CHOOSE i ∈ 1 ‥ Len(inbox[tpos]): inbox[tpos][i].type = "tok"
    IN inbox[tpos][idx]

(***************************************************************************)
(* EWD998 with channels refines EWD998 that models channels as sets.       *)
(***************************************************************************)
EWD998 ≜ INSTANCE EWD998 WITH token ←
                                  [pos   ↦ tpos, 
                                   q     ↦ token.q,
                                   color ↦ token.color],
                               pending ←
                                  \* Count the in-flight "pl" messages. The 
                                  \* inbox variable represents a node's network
                                  \* interface that receives arbitrary messages.
                                  \* However, EWD998 only "tracks" payload (pl)
                                  \* messages.
                                  [n ∈ Node ↦ 
                                     Len(SelectSeq(inbox[n], 
                                         LAMBDA msg: msg.type = "pl")) ]

\* TLC config doesn't accept the expression EWD998!Spec for PROPERTY.
\* Model-checked for N=3 and StateConstraint above on a laptop in ~15min.
EWD998Spec ≜ EWD998!Spec

THEOREM Spec ⇒ EWD998Spec

=============================================================================