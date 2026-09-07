import Common

-- Only a one-step expansion interface, not the reusable invariant theorem.
theorem child (P : Nat → Prop) (d i : Nat) :
    TreeOK P (Nat.succ d) i ↔
      TreeOK P d (2 * i) ∧ TreeOK P d (2 * i + 1) := Iff.rfl
