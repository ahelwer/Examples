--------------------------- MODULE KeyValueStore ---------------------------
(**************************************************************************)
(* A simple key-value store exhibiting snapshot isolation. If two         *)
(* concurrent transactions write to the same key, the one merging later   *)
(* will be rejected. If they write different keys both will succeed. For  *)
(* a more-detailed specification of snapshot isolation, look at the       *)
(* specifications/SnapshotIsolation specs in the tlaplus/examples repo.   *)
(**************************************************************************)

CONSTANTS   Key,            \* The set of all keys.
            Val,            \* The set of all values.
            TxId            \* The set of all transaction IDs.
VARIABLES   store,          \* A data store mapping keys to values.
            tx,             \* The set of open snapshot transactions.
            snapshotStore,  \* Snapshots of the store for each transaction.
            written,        \* A log of writes performed within each transaction.
            missed          \* The set of writes invisible to each transaction.
----------------------------------------------------------------------------
NoVal ≜    \* Choose something to represent the absence of a value.
    CHOOSE v : v ∉ Val

Store ≜    \* The set of all key-value stores.
    [Key → Val ∪ {NoVal}]

Init ≜ \* The initial predicate.
    ∧ store = [k ∈ Key ↦ NoVal]        \* All store values are initially NoVal.
    ∧ tx = {}                              \* The set of open transactions is initially empty.
    ∧ snapshotStore =                      \* All snapshotStore values are initially NoVal.
        [t ∈ TxId ↦ [k ∈ Key ↦ NoVal]]
    ∧ written = [t ∈ TxId ↦ {}]        \* All write logs are initially empty.
    ∧ missed = [t ∈ TxId ↦ {}]         \* All missed writes are initially empty.
    
TypeInvariant ≜    \* The type invariant.
    ∧ store ∈ Store
    ∧ tx ⊆ TxId
    ∧ snapshotStore ∈ [TxId → Store]
    ∧ written ∈ [TxId → SUBSET Key]
    ∧ missed ∈ [TxId → SUBSET Key]
    
TxLifecycle ≜
    ∧ ∀ t ∈ tx :    \* If store != snapshot & we haven't written it, we must have missed a write.
        ∀ k ∈ Key : (store[k] ≠ snapshotStore[t][k] ∧ k ∉ written[t]) ⇒ k ∈ missed[t]
    ∧ ∀ t ∈ TxId \ tx : \* Checks transactions are cleaned up after disposal.
        ∧ ∀ k ∈ Key : snapshotStore[t][k] = NoVal
        ∧ written[t] = {}
        ∧ missed[t] = {}

OpenTx(t) ≜    \* Open a new transaction.
    ∧ t ∉ tx
    ∧ tx' = tx ∪ {t}
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t] = store]
    ∧ UNCHANGED ⟨written, missed, store⟩

Add(t, k, v) ≜ \* Using transaction t, add value v to the store under key k.
    ∧ t ∈ tx
    ∧ snapshotStore[t][k] = NoVal
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    ∧ written' = [written EXCEPT ![t] = @ ∪ {k}]
    ∧ UNCHANGED ⟨tx, missed, store⟩
    
Update(t, k, v) ≜  \* Using transaction t, update the value associated with key k to v.
    ∧ t ∈ tx
    ∧ snapshotStore[t][k] ∉ {NoVal, v}
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t][k] = v]
    ∧ written' = [written EXCEPT ![t] = @ ∪ {k}]
    ∧ UNCHANGED ⟨tx, missed, store⟩
    
Remove(t, k) ≜ \* Using transaction t, remove key k from the store.
    ∧ t ∈ tx
    ∧ snapshotStore[t][k] ≠ NoVal
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t][k] = NoVal]
    ∧ written' = [written EXCEPT ![t] = @ ∪ {k}]
    ∧ UNCHANGED ⟨tx, missed, store⟩
    
RollbackTx(t) ≜    \* Close the transaction without merging writes into store.
    ∧ t ∈ tx
    ∧ tx' = tx \ {t}
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t] = [k ∈ Key ↦ NoVal]]
    ∧ written' = [written EXCEPT ![t] = {}]
    ∧ missed' = [missed EXCEPT ![t] = {}]
    ∧ UNCHANGED store

CloseTx(t) ≜   \* Close transaction t, merging writes into store.
    ∧ t ∈ tx
    ∧ missed[t] ∩ written[t] = {}   \* Detection of write-write conflicts.
    ∧ store' =                         \* Merge snapshotStore writes into store.
        [k ∈ Key ↦ IF k ∈ written[t] THEN snapshotStore[t][k] ELSE store[k]]
    ∧ tx' = tx \ {t}
    ∧ missed' =    \* Update the missed writes for other open transactions.
        [otherTx ∈ TxId ↦ IF otherTx ∈ tx' THEN missed[otherTx] ∪ written[t] ELSE {}]
    ∧ snapshotStore' = [snapshotStore EXCEPT ![t] = [k ∈ Key ↦ NoVal]]
    ∧ written' = [written EXCEPT ![t] = {}]

Next ≜ \* The next-state relation.
    ∨ ∃ t ∈ TxId : OpenTx(t)
    ∨ ∃ t ∈ tx : ∃ k ∈ Key : ∃ v ∈ Val : Add(t, k, v)
    ∨ ∃ t ∈ tx : ∃ k ∈ Key : ∃ v ∈ Val : Update(t, k, v)
    ∨ ∃ t ∈ tx : ∃ k ∈ Key : Remove(t, k)
    ∨ ∃ t ∈ tx : RollbackTx(t)
    ∨ ∃ t ∈ tx : CloseTx(t)
        
Spec ≜ \* Initialize state with Init and transition with Next.
    Init ∧ □[Next]_⟨store, tx, snapshotStore, written, missed⟩
----------------------------------------------------------------------------
THEOREM Spec ⇒ □(TypeInvariant ∧ TxLifecycle)
=============================================================================
