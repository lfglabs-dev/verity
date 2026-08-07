/- First-class Solidity narrow integers and fixed bytes. -/

import Verity.Core.Int256

namespace Verity.Core

/-- An unsigned integer bounded by `2^bits`. Solidity widths are validated by
the contract macro; keeping the carrier generic is useful in specifications. -/
structure UIntN (bits : Nat) where
  val : Nat
  isLt : val < 2 ^ bits
  deriving DecidableEq

namespace UIntN

theorem modulus_pos (bits : Nat) : 0 < 2 ^ bits := Nat.pow_pos (by decide)

def ofNat (bits : Nat) (n : Nat) : UIntN bits :=
  ⟨n % 2 ^ bits, Nat.mod_lt _ (modulus_pos bits)⟩

def ofUint256 (bits : Nat) (value : Uint256) : UIntN bits := ofNat bits value.val
def toNat (value : UIntN bits) : Nat := value.val
def toUint256 (value : UIntN bits) : Uint256 := Uint256.ofNat value.val

instance : OfNat (UIntN bits) n := ⟨ofNat bits n⟩
instance : Inhabited (UIntN bits) := ⟨ofNat bits 0⟩
instance : Repr (UIntN bits) := ⟨fun value _ => repr value.val⟩
instance : BEq (UIntN bits) := ⟨fun a b => decide (a = b)⟩
instance : LT (UIntN bits) := ⟨fun a b => a.val < b.val⟩
instance : LE (UIntN bits) := ⟨fun a b => a.val ≤ b.val⟩

def add (a b : UIntN bits) : UIntN bits := ofNat bits (a.val + b.val)
def sub (a b : UIntN bits) : UIntN bits :=
  if b.val ≤ a.val then ofNat bits (a.val - b.val)
  else ofNat bits (2 ^ bits - (b.val - a.val))
def mul (a b : UIntN bits) : UIntN bits := ofNat bits (a.val * b.val)
def div (a b : UIntN bits) : UIntN bits :=
  if b.val = 0 then ofNat bits 0 else ofNat bits (a.val / b.val)
def mod (a b : UIntN bits) : UIntN bits :=
  if b.val = 0 then ofNat bits 0 else ofNat bits (a.val % b.val)

def addOverflow (a b : UIntN bits) : Bool := a.val + b.val ≥ 2 ^ bits
def subUnderflow (a b : UIntN bits) : Bool := b.val > a.val
def mulOverflow (a b : UIntN bits) : Bool := a.val * b.val ≥ 2 ^ bits

instance : Add (UIntN bits) := ⟨add⟩
instance : Sub (UIntN bits) := ⟨sub⟩
instance : Mul (UIntN bits) := ⟨mul⟩
instance : Div (UIntN bits) := ⟨div⟩
instance : Mod (UIntN bits) := ⟨mod⟩

@[ext] theorem ext {a b : UIntN bits} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp_all

end UIntN

/-- A signed two's-complement integer of `bits` bits. `word` stores the low
bits, exactly matching Solidity explicit narrowing conversion. -/
structure IntN (bits : Nat) where
  word : UIntN bits
  deriving DecidableEq, Repr

namespace IntN

def ofInt (bits : Nat) (value : Int) : IntN bits :=
  ⟨UIntN.ofNat bits (value % (Int.ofNat (2 ^ bits))).toNat⟩

def ofUint256 (bits : Nat) (value : Uint256) : IntN bits :=
  ⟨UIntN.ofUint256 bits value⟩

def toInt (value : IntN bits) : Int :=
  if bits = 0 then 0
  else if value.word.val < 2 ^ (bits - 1) then Int.ofNat value.word.val
  else Int.ofNat value.word.val - Int.ofNat (2 ^ bits)

def toUint256 (value : IntN bits) : Uint256 :=
  Int256.toUint256 (Int256.ofInt value.toInt)

instance : OfNat (IntN bits) n := ⟨ofInt bits (Int.ofNat n)⟩
instance : Inhabited (IntN bits) := ⟨ofInt bits 0⟩
instance : BEq (IntN bits) := ⟨fun a b => decide (a = b)⟩
instance : LT (IntN bits) := ⟨fun a b => a.toInt < b.toInt⟩
instance : LE (IntN bits) := ⟨fun a b => a.toInt ≤ b.toInt⟩

def add (a b : IntN bits) : IntN bits := ofInt bits (a.toInt + b.toInt)
def sub (a b : IntN bits) : IntN bits := ofInt bits (a.toInt - b.toInt)
def mul (a b : IntN bits) : IntN bits := ofInt bits (a.toInt * b.toInt)
def div (a b : IntN bits) : IntN bits :=
  let lhs := a.toInt
  let rhs := b.toInt
  if rhs = 0 then ofInt bits 0
  else
    let quotient := lhs.natAbs / rhs.natAbs
    if (lhs < 0) == (rhs < 0) then ofInt bits (Int.ofNat quotient)
    else ofInt bits (-Int.ofNat quotient)
def mod (a b : IntN bits) : IntN bits :=
  let lhs := a.toInt
  let rhs := b.toInt
  if rhs = 0 then ofInt bits 0
  else
    let remainder := lhs.natAbs % rhs.natAbs
    if lhs < 0 then ofInt bits (-Int.ofNat remainder)
    else ofInt bits (Int.ofNat remainder)

instance : Add (IntN bits) := ⟨add⟩
instance : Sub (IntN bits) := ⟨sub⟩
instance : Mul (IntN bits) := ⟨mul⟩
instance : Div (IntN bits) := ⟨div⟩
instance : Mod (IntN bits) := ⟨mod⟩

end IntN

/-- Solidity `bytesN`, represented as the N-byte payload. ABI conversion
left-aligns it in the 32-byte word, as required for fixed bytes. -/
structure BytesN (bytes : Nat) where
  val : Nat
  isLt : val < 2 ^ (8 * bytes)
  deriving DecidableEq

namespace BytesN

def ofNat (bytes : Nat) (n : Nat) : BytesN bytes :=
  ⟨n % 2 ^ (8 * bytes), Nat.mod_lt _ (Nat.pow_pos (by decide))⟩

def toNat (value : BytesN bytes) : Nat := value.val
def toUint256 (value : BytesN bytes) : Uint256 :=
  Uint256.ofNat (value.val * 2 ^ (8 * (32 - bytes)))
def ofUint256 (bytes : Nat) (value : Uint256) : BytesN bytes :=
  ofNat bytes (value.val / 2 ^ (8 * (32 - bytes)))

instance : OfNat (BytesN bytes) n := ⟨ofNat bytes n⟩
instance : Inhabited (BytesN bytes) := ⟨ofNat bytes 0⟩
instance : Repr (BytesN bytes) := ⟨fun value _ => repr value.val⟩
instance : BEq (BytesN bytes) := ⟨fun a b => decide (a = b)⟩

end BytesN

end Verity.Core
