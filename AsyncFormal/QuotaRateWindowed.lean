module

public import Veil

/-! # sql-quota rate limits with one log per window

`QuotaRateShared` with one change: a key's log is kept per window, so a call
deletes and counts only the entries of gates with its own window. #452
implements it in `c12076a`.

Within one window's log an index stands for a count: `windowed` says the
admissions of window `x` inside any `x`-window hold distinct indices, so there
are at most `limit` of them. The database clock is assumed never to go back.
-/

veil module QuotaRateWindowed

type key
type slot
type window
type time

instantiate tot : TotalOrder time
open TotalOrder

immutable relation expired : window → time → time → Bool

individual now : time
relation entry : key → window → slot → time → Bool
relation admitted : key → slot → time → window → Bool

#gen_state

assumption [expired_is_older] expired X T S → le S T ∧ S ≠ T
assumption [expired_stays] expired X T S ∧ le T U → expired X U S
assumption [expired_downward] expired X T S ∧ le R S → expired X T R

after_init {
  entry K X I S := false
  admitted K I S X := false
}

-- The database clock advances.
action tick (t : time) {
  require le now t ∧ now ≠ t
  now := t
}

-- `async_quota_admit` by a gate with window `w` admits one request on index `i`.
action admit (k : key) (w : window) (i : slot) {
  entry K X I S := decide (entry K X I S ∧ ¬ (K = k ∧ X = w ∧ expired w now S))
  require ∀ s, ¬ entry k w i s
  entry k w i now := true
  admitted k i now w := true
}

-- `async_quota_admit` finds the window's log full after deleting what left it.
action refuse (k : key) (w : window) {
  entry K X I S := decide (entry K X I S ∧ ¬ (K = k ∧ X = w ∧ expired w now S))
  require ∀ i, ∃ s, entry k w i s
}

safety [windowed] admitted K I S X ∧ admitted K I U X ∧ le S U ∧ S ≠ U ∧ admitted K J T X ∧ le U T → expired X T S

invariant [entry_is_admission] entry K X I S → admitted K I S X
invariant [admitted_past] admitted K I S X → le S now
invariant [gone_is_expired] admitted K I S X ∧ ¬ entry K X I S → expired X now S
invariant [reuse_after_expiry] admitted K I S X ∧ admitted K I U X ∧ le S U ∧ S ≠ U → expired X U S

set_option veil.smt.trust false

#gen_spec

#model_check { key := Fin 1, slot := Fin 2, window := Fin 2, time := Fin 4 }
  { expired := fun w t s => decide (s.val + (if w.val = 0 then 1 else 3) ≤ t.val) }

#check_invariants

end QuotaRateWindowed
