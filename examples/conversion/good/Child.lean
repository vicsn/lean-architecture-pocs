import Common

open Buffer

-- Preserve the raw result; add the normalized interface once in the library.
theorem raw_child (n : Nat) : n < cells (zeros (Nat.succ n)) := by
  rw [cells_zeros]
  exact Nat.lt_succ_self n

theorem child (n : Nat) : n < Nat.succ n := by
  simpa only [cells_zeros] using raw_child n
