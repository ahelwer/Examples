---- MODULE MultiPaxos_MC ----
EXTENDS MultiPaxos

(****************************)
(* TLC config-related defs. *)
(****************************)
ConditionalPerm(set) ≜ IF Cardinality(set) > 1
                          THEN Permutations(set)
                          ELSE {}

SymmetricPerms ≜      ConditionalPerm(Replicas)
                  ∪ ConditionalPerm(Writes)
                  ∪ ConditionalPerm(Reads)

ConstMaxBallot ≜ 2

----------

(*************************)
(* Type check invariant. *)
(*************************)
TypeOK ≜ ∧ ∀ m ∈ msgs: m ∈ Messages
         ∧ ∀ s ∈ Replicas: node[s] ∈ NodeStates
         ∧ Len(pending) ≤ NumCommands
         ∧ Cardinality(Range(pending)) = Len(pending)
         ∧ ∀ c ∈ Range(pending): c ∈ Commands
         ∧ Len(observed) ≤ 2 * NumCommands
         ∧ Cardinality(Range(observed)) = Len(observed)
         ∧ Cardinality(reqsMade) ≥ Cardinality(acksRecv)
         ∧ ∀ e ∈ Range(observed): e ∈ ClientEvents

THEOREM Spec ⇒ □TypeOK

----------

(*******************************)
(* Linearizability constraint. *)
(*******************************)
ReqPosOfCmd(c) ≜ CHOOSE i ∈ 1‥Len(observed):
                        ∧ observed[i].type = "Req"
                        ∧ observed[i].cmd = c

AckPosOfCmd(c) ≜ CHOOSE i ∈ 1‥Len(observed):
                        ∧ observed[i].type = "Ack"
                        ∧ observed[i].cmd = c

ResultOfCmd(c) ≜ observed[AckPosOfCmd(c)].val

OrderIdxOfCmd(order, c) ≜ CHOOSE j ∈ 1‥Len(order): order[j] = c

LastWriteBefore(order, j) ≜
    LET k ≜ CHOOSE k ∈ 0‥(j-1):
                    ∧ (k = 0 ∨ order[k] ∈ Writes)
                    ∧ ∀ l ∈ (k+1)‥(j-1): order[l] ∈ Reads
    IN  IF k = 0 THEN "nil" ELSE order[k]

IsLinearOrder(order) ≜
    ∧ {order[j]: j ∈ 1‥Len(order)} = Commands
    ∧ ∀ j ∈ 1‥Len(order):
            ResultOfCmd(order[j]) = LastWriteBefore(order, j)

ObeysRealTime(order) ≜
    ∀ c1, c2 ∈ Commands:
        (AckPosOfCmd(c1) < ReqPosOfCmd(c2))
            ⇒ (OrderIdxOfCmd(order, c1) < OrderIdxOfCmd(order, c2))

Linearizability ≜
    terminated ⇒ 
        ∃ order ∈ [1‥NumCommands → Commands]:
            ∧ IsLinearOrder(order)
            ∧ ObeysRealTime(order)

THEOREM Spec ⇒ Linearizability

====