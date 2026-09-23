module

public import Veil

/-! # sql-quota rate limits, as in #452 at `640b603`

`async_quota_admit`: under the key's row lock, delete the key's log entries
older than the caller's window, then admit while fewer than `limit` remain.
Every gate on a key shares one log whatever its window.

Admissions are abstracted as slot indices: `slot` has `limit` elements and an
admission takes an index no remaining entry holds. A batch admits several at
the same instant, which is a sequence of single admissions with nothing in
between. `expired w t s` says an entry admitted at `s` has left window `w` at
time `t`; the database clock is assumed never to go back.

A gate promises at most `limit` admissions by gates with its window inside
any one of its windows. Indices stand for counts only when one log holds one
window's admissions, so `at_most_two` states the count directly for the
model-checked limit of two: no three admissions of one window lie inside it.

`#model_check` finds it violated in five steps: a gate with a three-tick window
admits twice at 0, filling the key; at 2 a gate with a one-tick window deletes
both entries as expired for its own window and admits once; the long-window
gate then admits a third time inside its window.
-/

veil module QuotaRateShared

type key
type slot
type window
type time

instantiate tot : TotalOrder time
open TotalOrder

immutable relation expired : window → time → time → Bool

individual now : time
relation entry : key → slot → time → Bool
relation admitted : key → slot → time → window → Bool

#gen_state

assumption [expired_is_older] expired X T S → le S T ∧ S ≠ T
assumption [expired_stays] expired X T S ∧ le T U → expired X U S
assumption [expired_downward] expired X T S ∧ le R S → expired X T R

after_init {
  entry K I S := false
  admitted K I S X := false
}

-- The database clock advances.
action tick (t : time) {
  require le now t ∧ now ≠ t
  now := t
}

-- `async_quota_admit` by a gate with window `w` admits one request on index `i`.
action admit (k : key) (w : window) (i : slot) {
  entry K I S := decide (entry K I S ∧ ¬ (K = k ∧ expired w now S))
  require ∀ s, ¬ entry k i s
  entry k i now := true
  admitted k i now w := true
}

-- `async_quota_admit` finds the key full after deleting what left the caller's window.
action refuse (k : key) (w : window) {
  entry K I S := decide (entry K I S ∧ ¬ (K = k ∧ expired w now S))
  require ∀ i, ∃ s, entry k i s
}

-- Three admissions by gates with window `x` inside one `x`-window ending at `t`.
ghost relation overfull (k : key) (x : window) :=
  ∃ i j l r u t, admitted k i r x ∧ admitted k j u x ∧ admitted k l t x ∧
    (i ≠ j ∨ r ≠ u) ∧ (i ≠ l ∨ r ≠ t) ∧ (j ≠ l ∨ u ≠ t) ∧
    le r t ∧ le u t ∧ ¬ expired x t r ∧ ¬ expired x t u

safety [at_most_two] ¬ overfull K X

#gen_spec

set_option veil.violationIsError false in
#model_check { key := Fin 1, slot := Fin 2, window := Fin 2, time := Fin 4 }
  { expired := fun w t s => decide (s.val + (if w.val = 0 then 1 else 3) ≤ t.val) }

end QuotaRateShared
