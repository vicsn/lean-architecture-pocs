import Child

set_option maxHeartbeats 0 in
set_option maxRecDepth 80008 in
theorem parent (P : Nat → Prop) (all : ∀ j, P j) (i : Nat) :
    TreeOK P 4 i := by
  simp (config := { maxSteps := 100000000 }) only
    [child, leaf, all, and_self]
