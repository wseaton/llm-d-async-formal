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
| `DispatchToken` | every dispatch writes a fresh token that all fences and maps compare; #452 implements it as `dispatch_attempt` in `249c497` | no violation in 1,577,504 states, and `#check_invariants` proves all 24 clauses inductive for unbounded nodes, keys, partitions, epochs and tokens |

`DispatchToken` sets `veil.smt.trust false` before `#gen_spec`, so cvc5's
answers are reconstructed into Lean proofs and checked by the kernel rather than
trusted. The option has no effect if set after `#gen_spec`.

## Conformance

The proof is about the model. `scripts/conformance.sh` checks the Go code
against it:

```
TEST_POSTGRES_URL=postgres://... scripts/conformance.sh <llm-d-async checkout> [seeds]
```

`TestModelTrace` in `producer-sql/sqlqueue` drives real `Consumer`s against
Postgres with a seeded random walk: polls, acks, retries, undispatches,
rebalances, lease lapses, crashes, and writes that fail before committing. It
also splits operations where production runs them concurrently: a store call
now and its bookkeeping later, `AcquirePartitions` before the `ResetStale` of
the next rebalance, and a dispatch that commits under a `Poll` error. Test-only
triggers record statement order. Each operation is written out as the model
steps it performed and the state it left: the tables plus each consumer's
in-flight, orphan and reconcile bookkeeping.

`replay` runs those steps in `DispatchToken`'s executable semantics. Every step
must be enabled, and after every operation the model state must equal the
recorded one.

Six injected bugs, each caught:

| Mutation | Traces rejected |
| --- | --- |
| `Ack` ignores the partition epoch | 1 / 100 |
| `Retry` ignores the owner | 1 / 400 |
| `Poll` keeps the orphan entry | 1 / 100 |
| `ResetStale` resets current-epoch rows | 84 / 100 |
| `doneStamps` ignores the attempt | 37 / 100 |
| `reconcileInFlight` trusts any tracked key | 5 / 100 |

The replay also found the model missing `pollFailed`: `Consumer.Poll` sets
`reconcile` on any `Dispatch` error, including one that never committed.
