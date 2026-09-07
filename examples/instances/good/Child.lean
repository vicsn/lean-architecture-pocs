import Common

def adapter0 (A : Type) [b : Backend 0 A] : Codec A :=
  b.codec

def adapter1 (A : Type) [b : Backend 1 A] : Codec A :=
  b.codec

def adapter2 (A : Type) [b : Backend 2 A] : Codec A :=
  b.codec

def adapter3 (A : Type) [b : Backend 3 A] : Codec A :=
  b.codec

def adapter4 (A : Type) [b : Backend 4 A] : Codec A :=
  b.codec

def adapter5 (A : Type) [b : Backend 5 A] : Codec A :=
  b.codec

def adapter6 (A : Type) [b : Backend 6 A] : Codec A :=
  b.codec

def adapter7 (A : Type) [b : Backend 7 A] : Codec A :=
  b.codec

theorem child {A : Type} [c : Codec A] (x : A) :
    c.decode (c.encode x) = x := c.roundtrip x
