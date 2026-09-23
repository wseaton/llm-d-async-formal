# llm-d-async-formal

[Veil](https://github.com/verse-lab/veil) models of llm-d-async's Postgres
transport (`producer-sql/sqlqueue`, llm-d/llm-d-async#452).

```
lake build
```

Each Postgres statement is one atomic action. A `Consumer` method is split where
the Go code splits it: the store call commits, and its `c.mu` bookkeeping runs
later. Lease expiry is not modelled, so any node may take any partition at any
time. `no_stranded_row` says a row stamped under its partition's current epoch
always has something that will finish it or return it to pending: a tracked
worker, an orphan entry, a pending reconcile, or a `Poll` still booking it.

| Module | Protocol | Result |
| --- | --- | --- |
| `SqlQueue` | #452 at `4ed4210` | `#model_check` finds a stranded row. Two `sat trace`s reproduce `TestConsumerRetryBookkeepingKeepsTheAttemptPollHandedOut` and `TestConsumerReconcileIgnoresTheBookkeepingOfAFinishedRetry`. |
| `CycleLock` | `Retry` and `Undispatch` hold `c.cycle` | no violation in 71,889 states (2 nodes, 3 epochs, 3 attempts) |
| `DispatchToken` | every dispatch writes a fresh token that all fences and maps compare | no violation in 1,577,504 states, and `#check_invariants` proves all 24 clauses inductive for unbounded nodes, keys, partitions, epochs and tokens |

`#check_invariants` trusts cvc5's unsat results unless
`set_option veil.smt.trust false` is set.
