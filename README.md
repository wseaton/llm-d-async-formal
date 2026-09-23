# llm-d-async-formal

Veil models of llm-d-async's Postgres transport (`producer-sql/sqlqueue`).

```
lake build
```

`AsyncFormal/SqlQueue.lean` models llm-d/llm-d-async#452 at `4ed4210`. Its
`#model_check` finds a stranded row, and two `sat trace`s reproduce the
races covered by `TestConsumerRetryBookkeepingKeepsTheAttemptPollHandedOut`
and `TestConsumerReconcileIgnoresTheBookkeepingOfAFinishedRetry`.
