module

public import Veil

/-! # llm-d-async sql transport with a dispatch token

`SqlQueue` with one change: `Store.Dispatch` writes a fresh token from a
Postgres sequence into the row, and every stamp carries it. Ack, Retry,
Undispatch and reconcile fence on the token, and `Consumer.inflight` and
`Consumer.orphans` remember it, so bookkeeping from one dispatch can never
match another dispatch under the same epoch.

The `attempt` sort is the token: it is drawn at dispatch, not at hand-out.
-/

veil module DispatchToken

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
relation stamped : key → epoch → attempt → Bool
relation result : key → epoch → Bool
relation owner : part → node → Bool
function pEpoch : part → epoch
relation draining : part → Bool

relation alive : node → Bool
relation polled : node → attempt → Bool
relation inflight : node → key → attempt → Bool
relation orphan : node → key → attempt → Bool
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
ghost relation polling (n : node) := ∃ a, polled n a

after_init {
  pending K := true
  stamped K E A := false
  result K E := false
  owner P N := false
  pEpoch P := e0
  draining P := false
  alive N := true
  polled N A := false
  inflight N K A := false
  orphan N K A := false
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
action resetStale (n : node) (k : key) (e : epoch) (a : attempt) {
  require alive n ∧ ¬ polling n ∧ owner (partOf k) n
  require stamped k e a ∧ le e (pEpoch (partOf k)) ∧ e ≠ pEpoch (partOf k)
  stamped k e a := false
  pending k := true
}

-- `Store.Dispatch` on one row, as seen by `Consumer.Poll`; the token comes from a sequence.
action dispatch (n : node) (k : key) {
  require alive n ∧ pending k
  require owner (partOf k) n ∧ ¬ draining (partOf k)
  let a :| ¬ used a
  let e := pEpoch (partOf k)
  pending k := false
  stamped k e a := true
  used a := true
  attNode a := n
  attKey a := k
  attEpoch a := e
  polled n a := true
}

-- `Store.Dispatch` committed but `Consumer.Poll` got an error back.
action dispatchLost (n : node) (k : key) {
  require alive n ∧ pending k
  require owner (partOf k) n ∧ ¬ draining (partOf k)
  let a :| ¬ used a
  let e := pEpoch (partOf k)
  pending k := false
  stamped k e a := true
  used a := true
  attNode a := n
  attKey a := k
  attEpoch a := e
  reconcile n := true
}

-- `Consumer.Poll` bookkeeping for one returned row, which then goes to a worker.
action book (a : attempt) {
  require alive (attNode a) ∧ polled (attNode a) a
  let n := attNode a
  let k := attKey a
  polled n a := false
  inflight n k A := false
  inflight n k a := true
  orphan n k A := false
  working a := true
}

-- `Store.Ack`: delete the row and record its result, fenced on token, owner and epoch.
action ackCommit (a : attempt) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if stamped k e a ∧ owner (partOf k) n ∧ pEpoch (partOf k) = e then
    stamped k e a := false
    result k e := true
  working a := false
  written a := true
}

-- `Store.Retry` or `Store.Undispatch`: back to pending, fenced on token and owner.
action requeueCommit (a : attempt) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if stamped k e a ∧ owner (partOf k) n then
    stamped k e a := false
    pending k := true
  working a := false
  written a := true
}

-- `Store.Ack` returned an error; the commit may or may not have landed.
action ackError (a : attempt) (landed : Bool) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if landed ∧ stamped k e a ∧ owner (partOf k) n ∧ pEpoch (partOf k) = e then
    stamped k e a := false
    result k e := true
  working a := false
  failed a := true
}

-- `Store.Retry` or `Store.Undispatch` returned an error; the commit may or may not have landed.
action requeueError (a : attempt) (landed : Bool) {
  require working a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  let e := attEpoch a
  if landed ∧ stamped k e a ∧ owner (partOf k) n then
    stamped k e a := false
    pending k := true
  working a := false
  failed a := true
}

-- `Consumer.doneStamps` after a written outcome.
action done (a : attempt) {
  require written a ∧ alive (attNode a)
  inflight (attNode a) (attKey a) a := false
  written a := false
}

-- `Consumer.Abandon` after a failed outcome.
action abandon (a : attempt) {
  require failed a ∧ alive (attNode a)
  let n := attNode a
  let k := attKey a
  if inflight n k a then
    orphan n k A := false
    orphan n k a := true
    inflight n k a := false
  failed a := false
}

-- `Consumer.undispatchOrphans` for one entry.
action undispatchOrphan (n : node) (k : key) (a : attempt) {
  require alive n ∧ ¬ polling n ∧ orphan n k a
  if stamped k (attEpoch a) a ∧ owner (partOf k) n then
    stamped k (attEpoch a) a := false
    pending k := true
  orphan n k a := false
}

-- `Consumer.reconcileInFlight`: return every current-epoch stamp of n's partitions it does not track.
action reconcileInFlight (n : node) {
  require alive n ∧ ¬ polling n ∧ reconcile n
  pending K := decide (pending K ∨ ∃ e a, stamped K e a ∧ owner (partOf K) n ∧ pEpoch (partOf K) = e ∧ ¬ inflight n K a)
  stamped K E A := decide (stamped K E A ∧ ¬ (owner (partOf K) n ∧ pEpoch (partOf K) = E ∧ ¬ inflight n K A))
  reconcile n := false
}

-- The dispatcher process dies; its rows stay stamped until someone acquires its partitions.
action crash (n : node) {
  require alive n
  alive n := false
  polled n A := false
  inflight n K A := false
  orphan n K A := false
  reconcile n := false
}

safety [one_result] result K E ∧ result K F → E = F
safety [no_loss] pending K ∨ (∃ e a, stamped K e a) ∨ (∃ e, result K e)
safety [result_consumes_row] result K E → ¬ pending K ∧ ¬ stamped K F A
invariant [one_stamp] stamped K E A ∧ stamped K F B → E = F ∧ A = B
invariant [stamp_or_pending] ¬ (pending K ∧ stamped K E A)

-- A row stamped under its partition's current epoch that nothing will ever finish or return.
ghost relation stranded (n : node) (k : key) (e : epoch) (a : attempt) :=
  stamped k e a ∧ owner (partOf k) n ∧ alive n ∧ pEpoch (partOf k) = e ∧
    ¬ (polled n a ∨ orphan n k a ∨ reconcile n ∨ (inflight n k a ∧ (working a ∨ failed a)))

safety [no_stranded_row] ¬ stranded N K E A

-- Bookkeeping facts `no_stranded_row` rests on.
invariant [stamp_names_its_row] stamped K E A → used A ∧ attKey A = K ∧ attEpoch A = E
invariant [stamp_not_ahead] stamped K E A → le E (pEpoch (partOf K))
invariant [current_stamp_is_owners] stamped K E A ∧ pEpoch (partOf K) = E ∧ owner (partOf K) N → attNode A = N
invariant [one_owner] owner P N ∧ owner P M → N = M
invariant [polled_fresh] polled N A → used A ∧ attNode A = N ∧ ¬ working A ∧ ¬ written A ∧ ¬ failed A
invariant [polled_under_current_lease] polled N A ∧ attKey A = K ∧ owner (partOf K) N → pEpoch (partOf K) = attEpoch A
invariant [polled_row_still_stamped] polled N A ∧ attKey A = K ∧ owner (partOf K) N → stamped K (attEpoch A) A
invariant [phases_exclusive] ¬ (working A ∧ written A) ∧ ¬ (working A ∧ failed A) ∧ ¬ (written A ∧ failed A)
invariant [phases_used] (working A ∨ written A ∨ failed A) → used A
invariant [inflight_names_attempt] inflight N K A → used A ∧ attKey A = K ∧ attNode A = N
invariant [inflight_one_per_key] inflight N K A ∧ inflight N K B → A = B
invariant [inflight_has_worker] inflight N K A → working A ∨ written A ∨ failed A
invariant [orphan_names_attempt] orphan N K A → used A ∧ attKey A = K ∧ attNode A = N
invariant [orphan_one_per_key] orphan N K A ∧ orphan N K B → A = B
invariant [inflight_or_orphan] ¬ (inflight N K A ∧ orphan N K B)
invariant [unused_is_untouched] ¬ used A → ¬ stamped K E A ∧ ¬ polled N A ∧ ¬ inflight N K A ∧ ¬ orphan N K A
invariant [written_is_settled] written A ∧ stamped K E A → ¬ (owner (partOf K) (attNode A) ∧ pEpoch (partOf K) = E)
invariant [dead_nodes_hold_nothing] ¬ alive N → ¬ polled N A ∧ ¬ inflight N K A ∧ ¬ orphan N K A ∧ ¬ reconcile N

#gen_spec

#model_check { node := Fin 2, key := Fin 1, part := Fin 1, epoch := Fin 3, attempt := Fin 4 }
  { partOf := fun _ => 0, e0 := 0 }

#check_invariants

sat trace [initial_state] { }

sat trace [can_complete] {
  acquire
  dispatch
  book
  ackCommit
  done
  assert (∃ k e, result k e)
}

sat trace [can_retry_then_complete] {
  acquire
  dispatch
  book
  requeueCommit
  done
  dispatch
  book
  ackCommit
  assert (∃ k e, result k e)
}

sat trace [can_fail_over_then_complete] {
  acquire
  dispatch
  book
  acquire
  resetStale
  dispatch
  book
  ackCommit
  assert (∃ k e n m a b, result k e ∧ attNode a = n ∧ attNode b = m ∧ n ≠ m ∧ used a ∧ used b)
}

unsat trace [retry_then_poll_cannot_strand] {
  acquire
  dispatch
  book
  requeueCommit
  dispatch
  book
  done
  assert (∃ n k e a, stranded n k e a)
}

unsat trace [retry_then_reconcile_cannot_strand] {
  acquire
  dispatch
  book
  requeueCommit
  dispatchLost
  reconcileInFlight
  done
  assert (∃ n k e a, stranded n k e a)
}

end DispatchToken
