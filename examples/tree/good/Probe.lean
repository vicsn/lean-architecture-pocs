import Child
import Metrics

#bench
set_option maxHeartbeats 0 in
set_option maxRecDepth 80008 in
theorem parent (P : Nat → Prop) (all : ∀ j, P j) (i : Nat) :
    TreeOK P 4 i := by
  exact child P all 4 i
