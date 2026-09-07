import Init

-- All leaves of a binary address tree satisfy P.
-- Distinct left/right addresses prevent the branches from being identical.
def TreeOK (P : Nat → Prop) : Nat → Nat → Prop
  | 0, i => P i
  | Nat.succ d, i => TreeOK P d (2 * i) ∧ TreeOK P d (2 * i + 1)

theorem leaf (P : Nat → Prop) (i : Nat) : TreeOK P 0 i ↔ P i := Iff.rfl
