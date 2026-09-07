import Common

-- One symbolic induction, available to every consumer.
theorem child (P : Nat → Prop) (all : ∀ j, P j) (d i : Nat) :
    TreeOK P d i := by
  induction d generalizing i with
  | zero => exact all i
  | succ d ih => exact And.intro (ih (2 * i)) (ih (2 * i + 1))
