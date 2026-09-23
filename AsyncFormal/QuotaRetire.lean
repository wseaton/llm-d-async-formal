module

public import Veil

/-! # sql-quota concurrency slots with holder retirement

`QuotaSlots` with one change: a quota statement that returns an error retires
the holder it ran under instead of being retried. A retired holder takes no
new grants, keeps renewing while any grant, queued release or statement in
flight still names it, and is deleted once none does. A grant whose reply was
lost, or a release that may not have landed, then disappears with its holder
rather than leaking or being subtracted twice. #452 implements it in `640b603`.

Slots are abstracted as in `QuotaSlots`: `slot` has `limit` elements and a
grant picks an index no live holder owns.
-/

veil module QuotaRetire

type proc
type holder
type key
type slot
type req

relation alive : proc → Bool
relation registered : holder → Bool
relation live : holder → Bool
relation retired : holder → Bool
function holderProc : holder → proc
relation current : proc → holder → Bool
relation owned : key → slot → holder → Bool

relation used : req → Bool
function reqProc : req → proc
function reqKey : req → key
relation waiting : req → Bool
relation abandoned : req → Bool
relation sent : req → holder → Bool
relation running : req → Bool
function runSlot : req → slot
function runHolder : req → holder
relation pendingRel : proc → key → slot → holder → Bool

#gen_state

-- Everything the process still knows about under `h`; a retired holder is deleted only without any.
ghost relation known (h : holder) :=
  (∃ r, running r ∧ runHolder r = h) ∨ (∃ p k i, pendingRel p k i h) ∨ (∃ r, sent r h)

after_init {
  alive P := true
  registered H := false
  live H := false
  retired H := false
  current P H := false
  owned K I H := false
  used R := false
  waiting R := false
  abandoned R := false
  sent R H := false
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

-- Retire the current holder: after a statement error, or a renewal the process cannot confirm.
action retire (p : proc) (h : holder) {
  require current p h
  current p h := false
  retired h := true
}

-- Delete a retired holder once nothing the process knows of names it.
action delete (h : holder) {
  require retired h ∧ live h ∧ alive (holderProc h) ∧ ¬ known h
  live h := false
}

-- The lease passes `expires_ms` without a renewal. The process renews every holder it
-- knows grants for, so this happens only once none of them is running.
action lapse (h : holder) {
  require live h
  require ∀ r, ¬ (running r ∧ runHolder r = h)
  live h := false
}

action submit (r : req) (p : proc) (k : key) {
  require alive p ∧ ¬ used r
  used r := true
  reqProc r := p
  reqKey r := k
  waiting r := true
  abandoned r := false
}

action abandon (r : req) {
  require waiting r ∧ ¬ abandoned r
  abandoned r := true
}

-- The key's batch sends `async_quota_acquire` under the current holder.
action send (r : req) (h : holder) {
  require waiting r ∧ alive (reqProc r) ∧ current (reqProc r) h
  require ∀ g, ¬ sent r g
  sent r h := true
}

-- The statement grants index `i`.
action grant (r : req) (h : holder) (i : slot) {
  require sent r h ∧ live h
  require ∀ g, ¬ (owned (reqKey r) i g ∧ live g)
  owned (reqKey r) i h := true
  sent r h := false
  waiting r := false
  if abandoned r then
    pendingRel (reqProc r) (reqKey r) i h := true
  else
    running r := true
    runSlot r := i
    runHolder r := h
}

-- The statement refuses: the key is full.
action refuse (r : req) (h : holder) {
  require sent r h
  sent r h := false
  waiting r := false
}

-- The statement finds the holder lapsed; the batch retires it and retries under a new one.
action holderLapsed (r : req) (h : holder) {
  require sent r h ∧ ¬ live h
  sent r h := false
  current (reqProc r) h := false
  retired h := true
}

-- The statement returns an error; `landed` says whether its grant committed anyway.
action acquireError (r : req) (h : holder) (i : slot) (landed : Bool) {
  require sent r h
  if landed ∧ live h ∧ ∀ g, ¬ (owned (reqKey r) i g ∧ live g) then
    owned (reqKey r) i h := true
  sent r h := false
  waiting r := false
  current (reqProc r) h := false
  retired h := true
}

action finish (r : req) {
  require running r ∧ alive (reqProc r)
  running r := false
  pendingRel (reqProc r) (reqKey r) (runSlot r) (runHolder r) := true
}

-- `ReleaseQuotaSlots` decrements `h`'s count for `k` once and is never retried. `ok` false
-- means it returned an error, which retires `h`; `landed` says whether it committed.
action release (p : proc) (k : key) (i : slot) (h : holder) (j : slot) (ok : Bool) (landed : Bool) {
  require alive p ∧ pendingRel p k i h
  require ok → landed
  require owned k i h → j = i
  if landed ∧ owned k j h then
    owned k j h := false
  pendingRel p k i h := false
  if ¬ ok then
    current p h := false
    retired h := true
}

action reap (h : holder) {
  require registered h ∧ ¬ live h
  owned K I h := false
}

action crash (p : proc) {
  require alive p
  alive p := false
  current p H := false
  pendingRel p K I H := false
  sent R H := decide (sent R H ∧ reqProc R ≠ p)
  waiting R := decide (waiting R ∧ reqProc R ≠ p)
  running R := decide (running R ∧ reqProc R ≠ p)
}

safety [exact] running R ∧ running S ∧ reqKey R = reqKey S ∧ runSlot R = runSlot S → R = S

-- A counted index nothing will release, under a holder that will never be deleted for it.
ghost relation leaked (k : key) (i : slot) (h : holder) :=
  owned k i h ∧ live h ∧ ¬ retired h ∧ alive (holderProc h) ∧
    ¬ ((∃ r, running r ∧ reqKey r = k ∧ runSlot r = i ∧ runHolder r = h) ∨ (∃ p, pendingRel p k i h))

safety [no_leak] ¬ leaked K I H

invariant [running_is_counted] running R → live (runHolder R) ∧ owned (reqKey R) (runSlot R) (runHolder R)
invariant [pending_is_counted] pendingRel P K I H ∧ live H → owned K I H
invariant [one_live_owner] owned K I H ∧ owned K I G ∧ live H ∧ live G → H = G
invariant [one_user_running] running R ∧ running S ∧ reqKey R = reqKey S ∧ runSlot R = runSlot S ∧ runHolder R = runHolder S → R = S
invariant [one_user_pending] ¬ (running R ∧ pendingRel P (reqKey R) (runSlot R) (runHolder R))
invariant [one_pending] pendingRel P K I H ∧ pendingRel Q K I H → P = Q
invariant [running_proc] running R → used R ∧ ¬ waiting R ∧ holderProc (runHolder R) = reqProc R ∧ alive (reqProc R)
invariant [pending_proc] pendingRel P K I H → holderProc H = P ∧ alive P ∧ registered H
invariant [sent_proc] sent R H → waiting R ∧ used R ∧ holderProc H = reqProc R ∧ registered H ∧ alive (reqProc R)
invariant [sent_once] sent R H ∧ sent R G → H = G
invariant [waiting_used] waiting R → used R ∧ alive (reqProc R)
invariant [current_proc] current P H → holderProc H = P ∧ registered H ∧ ¬ retired H ∧ alive P
invariant [current_one] current P H ∧ current P G → H = G
invariant [live_registered] (live H ∨ retired H) → registered H
invariant [owned_registered] owned K I H → registered H
invariant [running_registered] running R → registered (runHolder R)
invariant [fresh_is_untouched] ¬ registered H → ¬ (∃ r, running r ∧ runHolder r = H)
invariant [dead_proc_is_idle] ¬ alive P → ¬ current P H ∧ ¬ pendingRel P K I H

set_option veil.smt.trust false

#gen_spec

#model_check { proc := Fin 2, holder := Fin 2, key := Fin 1, slot := Fin 2, req := Fin 3 } { }

#check_invariants

sat trace [can_run_to_the_limit] {
  register
  submit
  send
  grant
  submit
  send
  grant
  assert (∃ r s, running r ∧ running s ∧ r ≠ s ∧ reqKey r = reqKey s)
}

sat trace [lost_release_is_recovered_by_delete] {
  register
  submit
  send
  grant
  finish
  release
  delete
  reap
  register
  submit
  send
  grant
  assert (∃ r, running r)
}

end QuotaRetire
