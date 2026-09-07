import Init

namespace Buffer

-- A simple immutable zero-initialized buffer and its structural size.
def zeros : Nat → List Nat
  | 0 => []
  | Nat.succ n => 0 :: zeros n

def cells : List Nat → Nat
  | [] => 0
  | _ :: xs => Nat.succ (cells xs)

theorem cells_zeros (n : Nat) : cells (zeros n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ ih

end Buffer
