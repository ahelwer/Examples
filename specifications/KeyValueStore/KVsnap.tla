--------------------------- MODULE KVsnap ---------------------------------
(**************************************************************************)
(* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
(* This version has atomic updates of store and missed sets of txns       *)
(**************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS   Key,            \* The set of all keys.
            TxId,           \* The set of all transaction IDs.
            NoVal           \* NoVal, which all keys are initialized with.

\* Instantiating ClientCentric enables us to check transaction isolation guarantees this model satisfies
\* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html         
CC ≜ INSTANCE ClientCentric WITH Keys ← Key, Values ← TxId ∪ {NoVal}          
    
\* for instantiating the ClientCentric module
wOp(k,v) ≜ CC!w(k,v)
rOp(k,v) ≜ CC!r(k,v)
InitialState ≜ [k ∈ Key ↦ NoVal]   
SetToSeq(S) ≜ CHOOSE f ∈ [1‥Cardinality(S) → S] : IsInjective(f)

(* --algorithm KVsnap {

variables 
    \* A data store mapping keys to values
    store = [k ∈ Key ↦ NoVal],

    \* The set of open snapshot transactions
    tx = {},

    \* The set of writes invisible to each transaction
    missed = [t ∈ TxId ↦ {}];

\* See end of file for invariants


\* Transaction processing
fair process (t ∈ TxId)
variables
    snapshotStore = [k ∈ Key ↦ NoVal], \* local snapshot of the store
    read_keys  = {},    \* read keys  for the transaction
    write_keys = {},    \* write keys for the transaction
    ops = ⟨⟩;   \* a log of reads & writes this transaction executes; used for interfacing to CC
{
START: \* Start the transaction
    tx ≔ tx ∪ {self};
    snapshotStore ≔ store; \* take my snapshot of store

    with (rk ∈ SUBSET Key \ { {} }; wk ∈ SUBSET Key \ { {} }) {
        read_keys ≔ rk;     \* select a random read-key-set  from possible read-keys
        write_keys ≔ wk;    \* select a random write-key-set from possible write-keys  
    };


READ: \* Process reads on my snapshot          
    \* log reads for CC isolation check 
    ops ≔ ops ∘ SetToSeq({rOp(k, snapshotStore[k]): k ∈ read_keys}); 
    
UPDATE: \* Process writes on my snapshot, write 'self' as value
    snapshotStore ≔ [k ∈ Key ↦ IF k ∈ write_keys THEN self ELSE snapshotStore[k] ];    

COMMIT: \* Commit the transaction to the database if there is no conflict   
    if (missed[self] ∩ write_keys = {}) { 
        \* take self off of active txn set
        tx ≔ tx \ {self}; 

        \* Update the missed writes for other open transactions (nonlocal update!)
        missed ≔ [o ∈ TxId ↦ IF o ∈ tx THEN missed[o] ∪ write_keys ELSE missed[o]];
        
        \* update store
        store ≔ [k ∈ Key ↦ IF k ∈ write_keys THEN snapshotStore[k] ELSE store[k] ];  
        
        \* log reads for CC isolation check 
        ops ≔ ops ∘ SetToSeq({wOp(k, self): k ∈ write_keys}); 
    }
}


}
*)

\* BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops

vars ≜ ⟨ store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops
        ⟩

ProcSet ≜ (TxId)

Init ≜ (* Global variables *)
        ∧ store = [k ∈ Key ↦ NoVal]
        ∧ tx = {}
        ∧ missed = [t ∈ TxId ↦ {}]
        (* Process t *)
        ∧ snapshotStore = [self ∈ TxId ↦ [k ∈ Key ↦ NoVal]]
        ∧ read_keys = [self ∈ TxId ↦ {}]
        ∧ write_keys = [self ∈ TxId ↦ {}]
        ∧ ops = [self ∈ TxId ↦ ⟨⟩]
        ∧ pc = [self ∈ ProcSet ↦ "START"]

START(self) ≜ ∧ pc[self] = "START"
              ∧ tx' = (tx ∪ {self})
              ∧ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
              ∧ ∃ rk ∈ SUBSET Key \ { {} }:
                    ∃ wk ∈ SUBSET Key \ { {} }:
                      ∧ read_keys' = [read_keys EXCEPT ![self] = rk]
                      ∧ write_keys' = [write_keys EXCEPT ![self] = wk]
              ∧ pc' = [pc EXCEPT ![self] = "READ"]
              ∧ UNCHANGED ⟨ store, missed, ops ⟩

READ(self) ≜ ∧ pc[self] = "READ"
             ∧ ops' = [ops EXCEPT ![self] = ops[self] ∘ SetToSeq({rOp(k, snapshotStore[self][k]): k ∈ read_keys[self]})]
             ∧ pc' = [pc EXCEPT ![self] = "UPDATE"]
             ∧ UNCHANGED ⟨ store, tx, missed, snapshotStore, read_keys, 
                              write_keys ⟩

UPDATE(self) ≜ ∧ pc[self] = "UPDATE"
               ∧ snapshotStore' = [snapshotStore EXCEPT ![self] = [k ∈ Key ↦ IF k ∈ write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
               ∧ pc' = [pc EXCEPT ![self] = "COMMIT"]
               ∧ UNCHANGED ⟨ store, tx, missed, read_keys, write_keys, ops ⟩

COMMIT(self) ≜ ∧ pc[self] = "COMMIT"
               ∧ IF missed[self] ∩ write_keys[self] = {}
                      THEN ∧ tx' = tx \ {self}
                           ∧ missed' = [o ∈ TxId ↦ IF o ∈ tx' THEN missed[o] ∪ write_keys[self] ELSE missed[o]]
                           ∧ store' = [k ∈ Key ↦ IF k ∈ write_keys[self] THEN snapshotStore[self][k] ELSE store[k] ]
                           ∧ ops' = [ops EXCEPT ![self] = ops[self] ∘ SetToSeq({wOp(k, self): k ∈ write_keys[self]})]
                      ELSE ∧ TRUE
                           ∧ UNCHANGED ⟨ store, tx, missed, ops ⟩
               ∧ pc' = [pc EXCEPT ![self] = "Done"]
               ∧ UNCHANGED ⟨ snapshotStore, read_keys, write_keys ⟩

t(self) ≜ START(self) ∨ READ(self) ∨ UPDATE(self) ∨ COMMIT(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating ≜ ∧ ∀ self ∈ ProcSet: pc[self] = "Done"
              ∧ UNCHANGED vars

Next ≜ (∃ self ∈ TxId: t(self))
           ∨ Terminating

Spec ≜ ∧ Init ∧ □[Next]_vars
       ∧ ∀ self ∈ TxId : WF_vars(t(self))

Termination ≜ ◇(∀ self ∈ ProcSet: pc[self] = "Done")

\* END TRANSLATION 



\* Snapshot isolation invariant
SnapshotIsolation ≜ CC!SnapshotIsolation(InitialState, Range(ops))

TypeOK ≜ \* type invariant
    ∧ store ∈ [Key → TxId ∪ {NoVal}]
    ∧ tx ⊆ TxId
    ∧ missed ∈ [TxId → SUBSET Key] 


\* Serializability would not be satisfied due to write-skew
Serialization ≜ CC!Serializability(InitialState, Range(ops))

===========================================================================
As an exercise try to add more yield points, make the actions smaller. 
Especially see if you can pull out something from the atomic "COMMIT" label to earlier, and see what breaks.


