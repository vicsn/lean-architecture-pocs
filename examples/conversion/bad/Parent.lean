import Child

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem parent : 256 < Nat.succ 256 := by
  exact child 256
