import Lean
import Lean.Util.Heartbeats

open Lean Elab Command

-- Command-elaboration heartbeats, not a replacement for whole-process timing.
elab "#bench " c:command : command => do
  let (_, raw) ← Lean.withHeartbeats (elabCommand c)
  logInfo m!"BENCH_HEARTBEATS_RAW={raw}"
