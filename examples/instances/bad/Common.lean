import Init

-- A reversible transformation. Identity is a lawful generic fallback.
class Codec (A : Type) where
  encode : A → A
  decode : A → A
  roundtrip : ∀ x, decode (encode x) = x

-- An optional implementation for one named backend.
class Backend (tag : Nat) (A : Type) where
  codec : Codec A

instance (priority := 100) fallback (A : Type) : Codec A where
  encode := id
  decode := id
  roundtrip _ := rfl
