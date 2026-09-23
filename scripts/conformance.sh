#!/usr/bin/env bash
# Record random traces from the Go sql transport and replay them against the DispatchToken model.
# Usage: TEST_POSTGRES_URL=postgres://... scripts/conformance.sh <llm-d-async checkout> [seeds]
set -euo pipefail

checkout=${1:?usage: scripts/conformance.sh <llm-d-async checkout> [seeds]}
seeds=${2:-100}
: "${TEST_POSTGRES_URL:?TEST_POSTGRES_URL must point at a scratch Postgres database}"

here=$(cd "$(dirname "$0")/.." && pwd)
traces=$(mktemp -d)
trap 'rm -rf "$traces"' EXIT

(cd "$checkout/producer-sql" &&
	SQLQUEUE_TRACE_DIR=$traces SQLQUEUE_TRACE_SEEDS=$seeds go test ./sqlqueue/ -run TestModelTrace -count=1)
(cd "$here" && lake build replay >/dev/null)
"$here/.lake/build/bin/replay" "$traces"/*.jsonl
