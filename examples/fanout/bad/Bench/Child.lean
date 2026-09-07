import Init

theorem child (n : Nat) : n + 0 = n := rfl

-- A specialized theorem, irrelevant to most consumers.
theorem auxiliary : 0 < 10 := by decide
