module

public import Veil

/-! # llm-d-async sql-quota concurrency slots, as in #452 at `d187fff`

`pkg/sqlflow/quota.go` over `async_quota_acquire` and `ReleaseQuotaSlots`.

The database keeps a count per key and holder, and a key is full when the
counts of live holders reach the limit. Counts are abstracted as slot indices:
`slot` has `limit` elements, `owned k i h` means holder `h`'s count for `k`
includes index `i`, and a statement that grants picks an index no live holder
owns. A decrement frees the index the finished request used if its holder
still owns it, and otherwise any other index of that holder, which is what a
bare count cannot tell apart.

`exact` says no two running requests share an index, so at most `limit` run.
-/

veil module QuotaSlots

type proc
type holder
type key
type slot
type req

relation alive : proc → Bool
relation registered : holder → Bool
relation live : holder → Bool
function holderProc : holder → proc
relation current : proc → holder → Bool
relation owned : key → slot → holder → Bool

relation used : req → Bool
function reqProc : req → proc
function reqKey : req → key
relation waiting : req → Bool
relation abandoned : req → Bool
relation running : req → Bool
function runSlot : req → slot
function runHolder : req → holder

-- A release `QuotaStore.release` queued, not yet confirmed by the database.
relation pendingRel : proc → key → slot → holder → Bool

#gen_state

after_init {
  alive P := true
  registered H := false
  live H := false
  current P H := false
  owned K I H := false
  used R := false
  waiting R := false
  abandoned R := false
  running R := false
  pendingRel P K I H := false
}

-- `QuotaStore.currentHolder`: register a fresh holder when the process has none.
action register (p : proc) (h : holder) {
  require alive p ∧ ¬ registered h
  require ∀ g, ¬ current p g
  registered h := true
  live h := true
  holderProc h := p
  current p h := true
}

-- `QuotaStore.dropHolder`, after a lapsed renewal or a lapsed acquire.
action drop (p : proc) (h : holder) {
  require current p h
  current p h := false
}

-- The holder's lease passes `expires_ms` without a renewal. Only while none of its
-- grants is running: a lapse under a running request frees a slot that is still in use.
action lapse (h : holder) {
  require live h
  require ∀ r, ¬ (running r ∧ runHolder r = h)
  live h := false
}

-- A worker calls `AcquireSlot` and waits in the key's batch.
action submit (r : req) (p : proc) (k : key) {
  require alive p ∧ ¬ used r
  used r := true
  reqProc r := p
  reqKey r := k
  waiting r := true
  abandoned r := false
}

-- The worker's context ends while it waits.
action abandon (r : req) {
  require waiting r ∧ ¬ abandoned r
  abandoned r := true
}

-- `async_quota_acquire` grants index `i` to `r`'s batch under the process's current holder.
action grant (r : req) (h : holder) (i : slot) {
  require waiting r ∧ alive (reqProc r) ∧ current (reqProc r) h ∧ live h
  require ∀ g, ¬ (owned (reqKey r) i g ∧ live g)
  owned (reqKey r) i h := true
  waiting r := false
  if abandoned r then
    pendingRel (reqProc r) (reqKey r) i h := true
  else
    running r := true
    runSlot r := i
    runHolder r := h
}

-- The batch was refused, or the statement failed before committing.
action refuse (r : req) {
  require waiting r
  waiting r := false
}

-- `async_quota_acquire` committed a grant but the reply was lost: every waiter gets the error.
action grantLost (r : req) (h : holder) (i : slot) {
  require waiting r ∧ alive (reqProc r) ∧ current (reqProc r) h ∧ live h
  require ∀ g, ¬ (owned (reqKey r) i g ∧ live g)
  owned (reqKey r) i h := true
  waiting r := false
}

-- The request finishes and its release is queued.
action finish (r : req) {
  require running r ∧ alive (reqProc r)
  running r := false
  pendingRel (reqProc r) (reqKey r) (runSlot r) (runHolder r) := true
}

-- `ReleaseQuotaSlots` decrements `h`'s count for `k` by one; `landed` false means
-- it returned an error after committing, so `flushReleases` keeps it queued.
action release (p : proc) (k : key) (i : slot) (h : holder) (j : slot) (landed : Bool) {
  require alive p ∧ pendingRel p k i h
  require owned k i h → j = i
  if owned k j h then
    owned k j h := false
  if landed then
    pendingRel p k i h := false
}

-- `ReapQuotaHolders` deletes a lapsed holder and its slot rows.
action reap (h : holder) {
  require registered h ∧ ¬ live h
  owned K I h := false
}

-- The process dies; its in-flight HTTP requests end with it.
action crash (p : proc) {
  require alive p
  alive p := false
  current p H := false
  pendingRel p K I H := false
  waiting R := decide (waiting R ∧ reqProc R ≠ p)
  running R := decide (running R ∧ reqProc R ≠ p)
}

safety [exact] running R ∧ running S ∧ reqKey R = reqKey S ∧ runSlot R = runSlot S → R = S

-- Every counted index is held by a running request or a queued release.
ghost relation leaked (k : key) (i : slot) (h : holder) :=
  owned k i h ∧ live h ∧ alive (holderProc h) ∧
    ¬ ((∃ r, running r ∧ reqKey r = k ∧ runSlot r = i ∧ runHolder r = h) ∨ (∃ p, pendingRel p k i h))

safety [no_leak] ¬ leaked K I H

#gen_spec

set_option veil.violationIsError false in
#model_check { proc := Fin 2, holder := Fin 2, key := Fin 1, slot := Fin 2, req := Fin 3 } { }

sat trace [can_run_to_the_limit] {
  register
  submit
  grant
  submit
  grant
  assert (∃ r s, running r ∧ running s ∧ r ≠ s ∧ reqKey r = reqKey s)
}

-- A release commits, its reply is lost, and the retry frees the slot of a request still running.
sat trace [retried_release_over_admits] {
  register
  submit
  grant
  submit
  grant
  finish
  release
  release
  submit
  grant
  assert (∃ r s, running r ∧ running s ∧ r ≠ s ∧ reqKey r = reqKey s ∧ runSlot r = runSlot s)
}

-- An acquire commits and its reply is lost: the slot counts for as long as the holder heartbeats.
sat trace [lost_grant_leaks] {
  register
  submit
  grantLost
  assert (∃ k i h, leaked k i h)
}

end QuotaSlots
