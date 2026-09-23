module

public import Veil

/-! # llm-d-async sql transport with Retry and Undispatch under `c.cycle`

`SqlQueue` with one change: `Consumer.Retry` and `Consumer.Undispatch` hold
`c.cycle` across the store call and its bookkeeping, so neither `Poll` nor
`Rebalance` runs between them. `Ack` is unchanged.

Every Postgres statement is one atomic action. A `Consumer` method is split
where the Go code splits it: the store call commits first, and the bookkeeping
under `c.mu` is a separate, later action. Lease expiry is not modelled; any
node may acquire any partition at any time, which covers every lapse.
-/

veil module CycleLock

type node
type key
type part
type epoch
type attempt

instantiate tot : TotalOrder epoch
open TotalOrder

immutable function partOf : key → part
immutable individual e0 : epoch

relation pending : key → Bool
relation stamped : key → epoch → Bool
relation result : key → epoch → Bool
relation owner : part → node → Bool
function pEpoch : part → epoch
relation draining : part → Bool

relation alive : node → Bool
relation polled : node → key → epoch → Bool
relation inflight : node → key → epoch → Bool
relation orphan : node → key → epoch → Bool
relation reconcile : node → Bool

relation used : attempt → Bool
function attNode : attempt → node
function attKey : attempt → key
function attEpoch : attempt → epoch
relation working : attempt → Bool
relation written : attempt → Bool
relation failed : attempt → Bool

#gen_state

assumption [e0_least] le e0 E

-- `Consumer.Poll` holds `c.cycle` from `Store.Dispatch` through its bookkeeping, and so does `Rebalance`.
ghost relation polling (n : node) := ∃ k e, polled n k e

after_init {
  pending K := true
  stamped K E := false
  result K E := false
  owner P N := false
  pEpoch P := e0
  draining P := false
  alive N := true
  polled N K E := false
  inflight N K E := false
  orphan N K E := false
  reconcile N := false
  used A := false
  working A := false
  written A := false
  failed A := false
}

-- `Store.AcquirePartitions`: take the partition and bump its epoch.
action acquire (n : node) (p : part) {
  require alive n ∧ ¬ polling n
  let e :| le (pEpoch p) e ∧ e ≠ pEpoch p
  owner p N := false
  owner p n := true
  pEpoch p := e
  draining p := false
}

-- `Store.ReleasePartitions` and `Store.Leave`.
action release (n : node) (p : part) {
  require alive n ∧ ¬ polling n ∧ owner p n
  owner p N := false
  draining p := false
}

-- `Store.SetDraining`.
action setDraining (n : node) (p : part) (d : Bool) {
  require alive n ∧ ¬ polling n ∧ owner p n
  draining p := d
}

-- `Store.ResetStale` on one row; `SKIP LOCKED` may leave any row for a later call.
action resetStale (n : node) (k : key) (e : epoch) {
  require alive n ∧ ¬ polling n ∧ owner (partOf k) n
  require stamped k e ∧ le e (pEpoch (partOf k)) ∧ e ≠ pEpoch (partOf k)
  stamped k e := false
  pending k := true
}

-- `Store.Dispatch` on one row, as seen by `Consumer.Poll`.
action dispatch (n : node) (k : key) {
  require alive n ∧ pending k
  require owner (partOf k) n ∧ ¬ draining (partOf k)
  let e := pEpoch (partOf k)
  pending k := false
  stamped k e := true
  polled n k e := true
}

-- `Store.Dispatch` committed but `Consumer.Poll` got an error back.
action dispatchLost (n : node) (k : key) {
  require alive n ∧ pending k
  require owner (partOf k) n ∧ ¬ draining (partOf k)
  let e := pEpoch (partOf k)
  pending k := false
  stamped k e := true
  reconcile n := true
}

-- `Consumer.Poll` bookkeeping for one returned row, which then goes to a worker.
action book (n : node) (k : key) (e : epoch) {
  require alive n ∧ polled n k e
  let a :| ¬ used a
  polled n k e := false
  inflight n k E := false
  inflight n k e := true
  orphan n k E := false
  used a := true
  attNode a := n
  attKey a := k
  attEpoch a := e
  working a := true
}

-- `Store.Ack`: delete the row and record its result, fenced on stamp, owner and epoch.
action ackCommit (a : attempt) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if stamped k e ∧ owner (partOf k) n ∧ pEpoch (partOf k) = e then
    stamped k e := false
    result k e := true
  working a := false
  written a := true
}

-- `Consumer.Retry` or `Consumer.Undispatch` under `c.cycle`: store call and `doneStamps` together.
action requeueCommit (a : attempt) {
  require working a ∧ alive (attNode a) ∧ ¬ polling (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if stamped k e ∧ owner (partOf k) n then
    stamped k e := false
    pending k := true
  if inflight n k e then
    inflight n k E := false
  working a := false
}

-- `Store.Ack` returned an error; the commit may or may not have landed.
action ackError (a : attempt) (landed : Bool) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if landed ∧ stamped k e ∧ owner (partOf k) n ∧ pEpoch (partOf k) = e then
    stamped k e := false
    result k e := true
  working a := false
  failed a := true
}

-- `Consumer.Retry` or `Consumer.Undispatch` under `c.cycle` whose store call errored: `Abandon` follows at once.
action requeueError (a : attempt) (landed : Bool) {
  require working a ∧ alive (attNode a) ∧ ¬ polling (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if landed ∧ stamped k e ∧ owner (partOf k) n then
    stamped k e := false
    pending k := true
  if inflight n k e then
    orphan n k E := false
    orphan n k e := true
    inflight n k E := false
  working a := false
}

-- `Consumer.doneStamps` after a written outcome.
action done (a : attempt) {
  require written a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if inflight n k e then
    inflight n k E := false
  written a := false
}

-- `Consumer.Abandon` after a failed outcome.
action abandon (a : attempt) {
  require failed a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if inflight n k e then
    orphan n k E := false
    orphan n k e := true
    inflight n k E := false
  failed a := false
}

-- `Consumer.undispatchOrphans` for one entry.
action undispatchOrphan (n : node) (k : key) (e : epoch) {
  require alive n ∧ ¬ polling n ∧ orphan n k e
  if stamped k e ∧ owner (partOf k) n then
    stamped k e := false
    pending k := true
  orphan n k e := false
}

-- `Consumer.reconcileInFlight`: return every current-epoch stamp of n's partitions it does not track.
action reconcileInFlight (n : node) {
  require alive n ∧ ¬ polling n ∧ reconcile n
  pending K := decide (pending K ∨ ∃ e, stamped K e ∧ owner (partOf K) n ∧ pEpoch (partOf K) = e ∧ ¬ inflight n K e)
  stamped K E := decide (stamped K E ∧ ¬ (owner (partOf K) n ∧ pEpoch (partOf K) = E ∧ ¬ inflight n K E))
  reconcile n := false
}

-- The dispatcher process dies; its rows stay stamped until someone acquires its partitions.
action crash (n : node) {
  require alive n
  alive n := false
  polled n K E := false
  inflight n K E := false
  orphan n K E := false
  reconcile n := false
}

safety [one_result] result K E ∧ result K F → E = F
safety [no_loss] pending K ∨ (∃ e, stamped K e) ∨ (∃ e, result K e)
safety [result_consumes_row] result K E → ¬ pending K ∧ ¬ stamped K F
invariant [one_stamp] stamped K E ∧ stamped K F → E = F
invariant [stamp_or_pending] ¬ (pending K ∧ stamped K E)

-- A row stamped under its partition's current epoch that nothing will ever finish or return.
ghost relation stranded (n : node) (k : key) (e : epoch) :=
  stamped k e ∧ owner (partOf k) n ∧ alive n ∧ pEpoch (partOf k) = e ∧
    ¬ (polled n k e ∨ orphan n k e ∨ reconcile n ∨
      (inflight n k e ∧ ∃ a, attNode a = n ∧ attKey a = k ∧ attEpoch a = e ∧ (working a ∨ failed a)))

safety [no_stranded_row] ¬ stranded N K E

#gen_spec

#model_check { node := Fin 2, key := Fin 1, part := Fin 1, epoch := Fin 3, attempt := Fin 3 }
  { partOf := fun _ => 0, e0 := 0 }

end CycleLock
