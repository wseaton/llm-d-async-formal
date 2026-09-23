import AsyncFormal.DispatchToken

open Lean DispatchToken

structure Observed where
  pending : List Nat
  stamped : List (List Nat)
  result : List Nat
  owner : List (List Nat)
  pEpoch : List (List Nat)
  draining : List Nat
  alive : List Nat
  polled : List (List Nat)
  inflight : List (List Nat)
  orphan : List (List Nat)
  reconcile : List Nat
  att : List (List Nat)
  working : List Nat
  written : List Nat
  failed : List Nat
  deriving BEq

def sortNats (xs : List Nat) : List Nat := (xs.eraseDups).mergeSort
def sortRows (xs : List (List Nat)) : List (List Nat) :=
  (xs.eraseDups).mergeSort (fun a b => compare a b != .gt)

def project (st : DispatchToken.TraceState) : Observed :=
  let used := st.used.toList.map (·.val)
  { pending := sortNats (st.pending.toList.map (·.val))
    stamped := sortRows (st.stamped.toList.map fun (k, e, a) => [k.val, e.val, a.val])
    result := sortNats (st.result.toList.map fun (k, _) => k.val)
    owner := sortRows (st.owner.toList.map fun (p, n) => [p.val, n.val])
    pEpoch := (List.finRange 64).map fun p => [p.val, (st.pEpoch.getD p default).val]
    draining := sortNats (st.draining.toList.map (·.val))
    alive := sortNats (st.alive.toList.map (·.val))
    polled := sortRows (st.polled.toList.map fun (n, a) => [n.val, a.val])
    inflight := sortRows (st.inflight.toList.map fun (n, k, a) => [n.val, k.val, a.val])
    orphan := sortRows (st.orphan.toList.map fun (n, k, a) => [n.val, k.val, a.val])
    reconcile := sortNats (st.reconcile.toList.map (·.val))
    att := sortRows ((List.finRange 256).filter (fun a => used.contains a.val) |>.map fun a =>
      [a.val, (st.attNode.getD a default).val, (st.attKey.getD a default).val, (st.attEpoch.getD a default).val])
    working := sortNats (st.working.toList.map (·.val))
    written := sortNats (st.written.toList.map (·.val))
    failed := sortNats (st.failed.toList.map (·.val)) }

def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .ok Json.null

def nats (j : Json) (name : String) : Except String (List Nat) := do
  match ← field j name with
  | .null => pure []
  | v => fromJson? v

def rows (j : Json) (name : String) : Except String (List (List Nat)) := do
  match ← field j name with
  | .null => pure []
  | v => fromJson? v

def observed (j : Json) : Except String Observed := do
  let pEpoch ← rows j "pEpoch"
  pure {
    pending := sortNats (← nats j "pending")
    stamped := sortRows (← rows j "stamped")
    result := sortNats (← nats j "result")
    owner := sortRows (← rows j "owner")
    pEpoch := (List.range 64).map fun p => [p, ((pEpoch.find? (·.head? == some p)).bind (·[1]?)).getD 0]
    draining := sortNats (← nats j "draining")
    alive := sortNats (← nats j "alive")
    polled := []
    inflight := sortRows (← rows j "inflight")
    orphan := sortRows (← rows j "orphan")
    reconcile := sortNats (← nats j "reconcile")
    att := sortRows (← rows j "att")
    working := sortNats (← nats j "working")
    written := sortNats (← nats j "written")
    failed := sortNats (← nats j "failed") }

def diff (model obs : Observed) : List String :=
  let check {α} [BEq α] [ToString α] (name : String) (m o : α) : List String :=
    if m == o then [] else [s!"  {name}: model {m}\n  {String.ofList (List.replicate name.length ' ')}  code  {o}"]
  check "pending" model.pending obs.pending ++ check "stamped" model.stamped obs.stamped ++
  check "result" model.result obs.result ++ check "owner" model.owner obs.owner ++
  check "pEpoch" model.pEpoch obs.pEpoch ++ check "draining" model.draining obs.draining ++
  check "alive" model.alive obs.alive ++ check "polled" model.polled obs.polled ++
  check "inflight" model.inflight obs.inflight ++ check "orphan" model.orphan obs.orphan ++
  check "reconcile" model.reconcile obs.reconcile ++ check "att" model.att obs.att ++
  check "working" model.working obs.working ++ check "written" model.written obs.written ++
  check "failed" model.failed obs.failed

def theoryOf (header : Json) : Except String DispatchToken.TraceTheory := do
  let partOf : List Nat ← fromJson? (← header.getObjVal? "partOf")
  let parts ← partOf.mapM (traceFin 64 "part")
  let parts := parts.toArray
  pure { partOf := fun k => parts.getD k.val 0, e0 := 0 }

/-- Replays one trace; returns the number of operations and steps, or the first disagreement. -/
def replay (lines : List String) : Except String (Nat × Nat) := do
  let header :: body := lines | throw "empty trace"
  let th ← theoryOf (← Json.parse header)
  let mut st ← traceOne "initializer" (traceInit th)
  let mut steps := 0
  for (line, i) in body.zipIdx do
    let j ← Json.parse line
    let op : String ← fromJson? (← j.getObjVal? "op")
    let recorded : List Json ← match ← field j "steps" with
      | .null => pure []
      | v => fromJson? v
    for step in recorded do
      let act : String ← fromJson? (← step.getObjVal? "act")
      let args : List Nat ← fromJson? (← step.getObjVal? "args")
      st ← match traceStep th st act args with
        | .ok st' => pure st'
        | .error e => throw s!"operation {i} `{op}`: {e}"
      steps := steps + 1
    let obs ← observed (← j.getObjVal? "state")
    let d := diff (project st) obs
    unless d.isEmpty do
      throw s!"operation {i} `{op}`: model and code disagree after {recorded.length} steps\n{String.intercalate "\n" d}"
  pure (body.length, steps)

def main (files : List String) : IO UInt32 := do
  let mut failures := 0
  let mut ops := 0
  let mut steps := 0
  for file in files do
    let lines := (← IO.FS.lines file).toList.filter (!·.isEmpty)
    match replay lines with
    | .ok (o, s) =>
      ops := ops + o
      steps := steps + s
    | .error e =>
      failures := failures + 1
      IO.eprintln s!"{file}\n{e}"
  IO.println s!"{files.length - failures}/{files.length} traces conform ({ops} operations, {steps} model steps)"
  pure (if failures == 0 then 0 else 1)
