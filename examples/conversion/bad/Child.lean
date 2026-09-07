import Common

open Buffer

-- Exposes the implementation-derived size to numerical-capacity clients.
theorem child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n
