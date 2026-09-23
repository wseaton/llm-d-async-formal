import Lake
open Lake DSL

require veil from git "https://github.com/verse-lab/veil.git" @ "517f2badbf9a7ba2b18a72242351ff20943cbdd7"

package «llm-d-async-formal»

@[default_target]
lean_lib AsyncFormal

lean_exe replay where
  root := `Replay
