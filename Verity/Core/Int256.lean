import Verity.Core.Uint256

namespace Verity.Core

structure Int256 where
  word : Uint256
  deriving DecidableEq

namespace Int256

def modulus : Nat := Uint256.modulus

def signBit : Nat := 2 ^ 255

def minValue : Int := -Int.ofNat signBit

def maxValue : Int := Int.ofNat signBit - 1

def ofUint256 (value : Uint256) : Int256 := ⟨value⟩

def toUint256 (value : Int256) : Uint256 := value.word

def toInt (value : Int256) : Int :=
  let raw : Nat := value.word
  if raw < signBit then
    Int.ofNat raw
  else
    Int.ofNat raw - Int.ofNat modulus

def ofInt (value : Int) : Int256 :=
  if value < 0 then
    ofUint256 <| Uint256.ofNat (modulus - (Int.natAbs value % modulus))
  else
    ofUint256 <| Uint256.ofNat value.toNat

instance : Inhabited Int256 := ⟨ofUint256 0⟩
instance : Repr Int256 := ⟨fun value _ => repr value.toInt⟩
instance : OfNat Int256 n := ⟨ofUint256 n⟩
instance : Coe Int256 Uint256 := ⟨toUint256⟩
instance : Coe Int256 Int := ⟨toInt⟩
instance : Coe Uint256 Int256 := ⟨ofUint256⟩

@[simp] theorem toUint256_ofUint256 (value : Uint256) :
    toUint256 (ofUint256 value) = value := rfl

@[simp] theorem ofUint256_toUint256 (value : Uint256) :
    (ofUint256 value : Int256).toUint256 = value := rfl

@[simp] theorem ofInt_nonneg (value : Int) (h : ¬ value < 0) :
    (ofInt value).toUint256 = Uint256.ofNat value.toNat := by
  simp [ofInt, h]

@[simp] theorem ofInt_neg (value : Int) (h : value < 0) :
    (ofInt value).toUint256 = Uint256.ofNat (modulus - (Int.natAbs value % modulus)) := by
  simp [ofInt, h]

@[simp] theorem toInt_of_lt_signBit {value : Int256} (h : value.word.val < signBit) :
    (value : Int) = Int.ofNat value.word.val := by
  simp [Int256.toInt, h]

@[simp] theorem toInt_of_ge_signBit {value : Int256} (h : signBit ≤ value.word.val) :
    (value : Int) = Int.ofNat value.word.val - Int.ofNat modulus := by
  have h' : ¬ value.word.val < signBit := Nat.not_lt_of_ge h
  simp [Int256.toInt, h']

theorem signBit_lt_modulus : signBit < modulus := by
  change (2 : Nat) ^ 255 < 2 ^ 256
  exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : 255 < 256)

theorem modulus_eq_two_mul_signBit : modulus = 2 * signBit := by
  change (2 : Nat) ^ 256 = 2 * 2 ^ 255
  have h : (256 : Nat) = 255 + 1 := rfl
  rw [h, Nat.pow_succ, Nat.mul_comm]

theorem minValue_le (value : Int256) : minValue ≤ (value : Int) := by
  by_cases h : value.word.val < signBit
  · simp [toInt_of_lt_signBit h, minValue]
  · have hge : signBit ≤ value.word.val := Nat.le_of_not_lt h
    have hraw : value.word.val < modulus := value.word.isLt
    simp [toInt_of_ge_signBit hge, minValue, modulus_eq_two_mul_signBit]
    omega

theorem le_maxValue (value : Int256) : (value : Int) ≤ maxValue := by
  by_cases h : value.word.val < signBit
  · simp [toInt_of_lt_signBit h, maxValue]
    omega
  · have hge : signBit ≤ value.word.val := Nat.le_of_not_lt h
    have hraw : value.word.val < modulus := value.word.isLt
    have hneg : (value : Int) ≤ -1 := by
      simp [toInt_of_ge_signBit hge]
      omega
    have hs : (0 : Int) ≤ Int.ofNat signBit := by
      simp
    have hmax : (-1 : Int) ≤ maxValue := by
      simp [maxValue]
      omega
    omega

theorem toInt_in_range (value : Int256) : minValue ≤ (value : Int) ∧ (value : Int) ≤ maxValue := by
  exact ⟨minValue_le value, le_maxValue value⟩

@[simp] theorem val_zero : ((0 : Int256) : Int) = 0 := by
  have hw : (0 : Int256).word = (0 : Uint256) := rfl
  have hpos : (0 : Nat) < signBit := by
    change (0 : Nat) < 2 ^ 255
    exact Nat.pow_pos (by decide : (0 : Nat) < 2)
  unfold Int256.toInt
  rw [hw]
  simp [Uint256.val_zero, hpos]

@[simp] theorem val_one : ((1 : Int256) : Int) = 1 := by
  have hw : (1 : Int256).word = (1 : Uint256) := rfl
  have hlt : (1 : Nat) < signBit := by
    change (2 : Nat) ^ 0 < 2 ^ 255
    exact Nat.pow_lt_pow_right (by decide : (1 : Nat) < 2) (by decide : 0 < 255)
  unfold Int256.toInt
  rw [hw]
  simp [Uint256.val_one, hlt]

def add (a b : Int256) : Int256 := ofUint256 (a.word + b.word)

def sub (a b : Int256) : Int256 := ofUint256 (a.word - b.word)

def mul (a b : Int256) : Int256 := ofUint256 (a.word * b.word)

def neg (value : Int256) : Int256 := ofUint256 <| Uint256.ofNat (modulus - value.word.val)

/-- Absolute value as `Nat`. Exposed for downstream bridge proofs. -/
def signedAbsNat (value : Int) : Nat := Int.natAbs value

def div (a b : Int256) : Int256 :=
  let lhs : Int := a
  let rhs : Int := b
  if rhs = 0 then
    0
  else
    let quotient := signedAbsNat lhs / signedAbsNat rhs
    let sameSign := (lhs < 0) == (rhs < 0)
    if sameSign then
      ofInt (Int.ofNat quotient)
    else
      ofInt (-Int.ofNat quotient)

def mod (a b : Int256) : Int256 :=
  let lhs : Int := a
  let rhs : Int := b
  if rhs = 0 then
    0
  else
    let remainder := signedAbsNat lhs % signedAbsNat rhs
    if lhs < 0 then
      ofInt (-Int.ofNat remainder)
    else
      ofInt (Int.ofNat remainder)

def sar (shift value : Int256) : Int256 :=
  let s := shift.word.val % modulus
  let v : Int := value
  if s ≥ 256 then
    if v < 0 then ofInt (-1) else 0
  else
    ofInt (Int.fdiv v (Int.ofNat (2 ^ s)))

def isNeg (value : Int256) : Bool :=
  signBit ≤ value.word.val

def isZero (value : Int256) : Bool :=
  value.word.val = 0

/-- Signed less-than. Lowers to Yul `slt` from `verity_contract` bodies. -/
def slt (a b : Int256) : Bool := decide ((a : Int) < (b : Int))

/-- Signed greater-than. Lowers to Yul `sgt`. -/
def sgt (a b : Int256) : Bool := decide ((a : Int) > (b : Int))

/-- Signed less-or-equal. Lowers to Yul `iszero(sgt(...))`. -/
def sle (a b : Int256) : Bool := decide ((a : Int) ≤ (b : Int))

/-- Signed greater-or-equal. Lowers to Yul `iszero(slt(...))`. -/
def sge (a b : Int256) : Bool := decide ((a : Int) ≥ (b : Int))

/-- True iff `z` is a representable `int256` value. -/
def inRange (z : Int) : Prop :=
  minValue ≤ z ∧ z ≤ maxValue

/-- Solidity 0.8 overflow condition for signed addition. -/
def addOverflows (a b : Int256) : Prop :=
  ¬ inRange ((a : Int) + (b : Int))

/-- Solidity 0.8 overflow condition for signed subtraction. -/
def subOverflows (a b : Int256) : Prop :=
  ¬ inRange ((a : Int) - (b : Int))

/-- Solidity 0.8 overflow condition for signed multiplication. -/
def mulOverflows (a b : Int256) : Prop :=
  ¬ inRange ((a : Int) * (b : Int))

/-- Solidity 0.8 failure for signed division: divide-by-zero or `minValue / -1`. -/
def divFails (a b : Int256) : Prop :=
  (b : Int) = 0 ∨ ((a : Int) = minValue ∧ (b : Int) = -1)

/-- Solidity 0.8 overflow condition for signed negation. -/
def negOverflows (value : Int256) : Prop :=
  (value : Int) = minValue

/-- Solidity 0.8 failure for signed modulo: divide-by-zero only. -/
def modFails (b : Int256) : Prop :=
  (b : Int) = 0

/-- Checked signed addition. `none` iff the mathematical sum is out of `int256` range. -/
def safeAdd (a b : Int256) : Option Int256 :=
  let s : Int := (a : Int) + (b : Int)
  if minValue ≤ s ∧ s ≤ maxValue then some (a.add b) else none

/-- Checked signed subtraction. `none` iff the mathematical difference is out of range. -/
def safeSub (a b : Int256) : Option Int256 :=
  let d : Int := (a : Int) - (b : Int)
  if minValue ≤ d ∧ d ≤ maxValue then some (a.sub b) else none

/-- Checked signed multiplication. `none` iff the mathematical product is out of range. -/
def safeMul (a b : Int256) : Option Int256 :=
  let p : Int := (a : Int) * (b : Int)
  if minValue ≤ p ∧ p ≤ maxValue then some (a.mul b) else none

/-- Checked signed division. `none` on divide-by-zero and on `minValue / -1`. -/
def safeDiv (a b : Int256) : Option Int256 :=
  if (b : Int) = 0 ∨ ((a : Int) = minValue ∧ (b : Int) = -1) then
    none
  else
    some (a.div b)

/-- Checked signed negation. `none` iff `value = minValue`. -/
def safeNeg (value : Int256) : Option Int256 :=
  if (value : Int) = minValue then none else some (neg value)

/-- Checked signed modulo. `none` iff the divisor is zero. -/
def safeMod (a b : Int256) : Option Int256 :=
  if (b : Int) = 0 then none else some (a.mod b)

/-- Solidity 0.8 panic-on-overflow addition, Option form.
    `none` is `Panic(0x11)`. The `Contract` wrappers live in `Verity.Stdlib.Math`. -/
def addPanic (a b : Int256) : Option Int256 := safeAdd a b

/-- Solidity 0.8 panic-on-overflow subtraction, Option form. `none` is `Panic(0x11)`. -/
def subPanic (a b : Int256) : Option Int256 := safeSub a b

/-- Solidity 0.8 panic-on-overflow multiplication, Option form. `none` is `Panic(0x11)`. -/
def mulPanic (a b : Int256) : Option Int256 := safeMul a b

/-- Solidity 0.8 panic-on-failure division, Option form.
    `none` covers both `Panic(0x12)` (divide-by-zero) and `Panic(0x11)` (`minValue / -1`). -/
def divPanic (a b : Int256) : Option Int256 := safeDiv a b

/-- Solidity 0.8 panic-on-overflow negation, Option form. `none` is `Panic(0x11)`. -/
def negPanic (value : Int256) : Option Int256 := safeNeg value

/-- Solidity 0.8 panic-on-zero-divisor modulo, Option form. `none` is `Panic(0x12)`. -/
def modPanic (a b : Int256) : Option Int256 := safeMod a b

instance : LT Int256 := ⟨fun a b => (a : Int) < (b : Int)⟩
instance : LE Int256 := ⟨fun a b => (a : Int) ≤ (b : Int)⟩
instance (a b : Int256) : Decidable (a < b) := by
  change Decidable ((a : Int) < (b : Int))
  infer_instance
instance (a b : Int256) : Decidable (a ≤ b) := by
  change Decidable ((a : Int) ≤ (b : Int))
  infer_instance

@[simp] theorem le_def (a b : Int256) : (a ≤ b) = ((a : Int) ≤ (b : Int)) := rfl
@[simp] theorem lt_def (a b : Int256) : (a < b) = ((a : Int) < (b : Int)) := rfl

instance : HAdd Int256 Int256 Int256 := ⟨add⟩
instance : HSub Int256 Int256 Int256 := ⟨sub⟩
instance : HMul Int256 Int256 Int256 := ⟨mul⟩
instance : HDiv Int256 Int256 Int256 := ⟨div⟩
instance : HMod Int256 Int256 Int256 := ⟨mod⟩
instance : Add Int256 := ⟨add⟩
instance : Sub Int256 := ⟨sub⟩
instance : Mul Int256 := ⟨mul⟩
instance : Div Int256 := ⟨div⟩
instance : Mod Int256 := ⟨mod⟩
instance : Neg Int256 := ⟨neg⟩

@[simp] theorem add_toUint256 (a b : Int256) :
    (a + b).toUint256 = a.toUint256 + b.toUint256 := rfl

@[simp] theorem sub_toUint256 (a b : Int256) :
    (a - b).toUint256 = a.toUint256 - b.toUint256 := rfl

@[simp] theorem mul_toUint256 (a b : Int256) :
    (a * b).toUint256 = a.toUint256 * b.toUint256 := rfl

@[simp] theorem neg_toUint256 (value : Int256) :
    (-value).toUint256 = Uint256.ofNat (modulus - value.word.val) := rfl

@[simp] theorem div_by_zero (value : Int256) : value / (0 : Int256) = 0 := by
  simp [HDiv.hDiv, Int256.div]

@[simp] theorem mod_by_zero (value : Int256) : value % (0 : Int256) = 0 := by
  simp [HMod.hMod, Int256.mod]

@[ext] theorem ext {a b : Int256} (h : a.word = b.word) : a = b := by
  cases a
  cases b
  cases h
  rfl

theorem ext_val {a b : Int256} (h : a.word.val = b.word.val) : a = b := by
  apply ext
  exact Uint256.ext h

theorem signBit_pos : 0 < signBit := by
  decide

theorem modulus_pos : 0 < modulus :=
  Nat.lt_trans signBit_pos signBit_lt_modulus

theorem inRange_toInt (value : Int256) : inRange (value : Int) :=
  toInt_in_range value

instance (z : Int) : Decidable (inRange z) :=
  inferInstanceAs (Decidable (minValue ≤ z ∧ z ≤ maxValue))

theorem add_word (a b : Int256) :
    (a.add b).word.val = (a.word.val + b.word.val) % modulus := by
  simp [add, ofUint256, HAdd.hAdd, Uint256.add, Uint256.val_ofNat, modulus]

theorem mul_word (a b : Int256) :
    (a.mul b).word.val = (a.word.val * b.word.val) % modulus := by
  simp [mul, ofUint256, HMul.hMul, Uint256.mul, Uint256.val_ofNat, modulus]

/-! ### Checked-arithmetic Option lemmas

Each `*Panic` success case is the wrapping operation. Failure is exactly the
Solidity 0.8 out-of-range / divide-by-zero / `minValue / -1` condition.
The wrapping result equals the mathematical `Int` result on the success
side; that identification is `toInt_add_of_inRange` and friends, proved
from two's-complement residue uniqueness. -/

theorem addPanic_success (a b : Int256)
    (h : minValue ≤ (a : Int) + (b : Int) ∧ (a : Int) + (b : Int) ≤ maxValue) :
    addPanic a b = some (a.add b) := by
  unfold addPanic safeAdd
  simp [h]

theorem addPanic_failure (a b : Int256)
    (h : ¬ (minValue ≤ (a : Int) + (b : Int) ∧ (a : Int) + (b : Int) ≤ maxValue)) :
    addPanic a b = none := by
  unfold addPanic safeAdd
  simp [h]

theorem subPanic_success (a b : Int256)
    (h : minValue ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ maxValue) :
    subPanic a b = some (a.sub b) := by
  unfold subPanic safeSub
  simp [h]

theorem subPanic_failure (a b : Int256)
    (h : ¬ (minValue ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ maxValue)) :
    subPanic a b = none := by
  unfold subPanic safeSub
  simp [h]

theorem mulPanic_success (a b : Int256)
    (h : minValue ≤ (a : Int) * (b : Int) ∧ (a : Int) * (b : Int) ≤ maxValue) :
    mulPanic a b = some (a.mul b) := by
  unfold mulPanic safeMul
  simp [h]

theorem mulPanic_failure (a b : Int256)
    (h : ¬ (minValue ≤ (a : Int) * (b : Int) ∧ (a : Int) * (b : Int) ≤ maxValue)) :
    mulPanic a b = none := by
  unfold mulPanic safeMul
  simp [h]

theorem divPanic_failure (a b : Int256) (h : divFails a b) :
    divPanic a b = none := by
  unfold divPanic safeDiv
  split
  · rfl
  · next hne => exact (hne h).elim

theorem divPanic_success (a b : Int256) (h : ¬ divFails a b) :
    divPanic a b = some (a.div b) := by
  unfold divPanic safeDiv
  split
  · next he => exact (h he).elim
  · rfl

theorem negPanic_success (value : Int256) (h : (value : Int) ≠ minValue) :
    negPanic value = some (neg value) := by
  unfold negPanic safeNeg
  simp [h]

theorem negPanic_failure (value : Int256) (h : (value : Int) = minValue) :
    negPanic value = none := by
  unfold negPanic safeNeg
  simp [h]

theorem modPanic_failure (a b : Int256) (h : (b : Int) = 0) :
    modPanic a b = none := by
  unfold modPanic safeMod
  simp [h]

theorem modPanic_success (a b : Int256) (h : (b : Int) ≠ 0) :
    modPanic a b = some (a.mod b) := by
  unfold modPanic safeMod
  simp [h]

theorem slt_iff (a b : Int256) : slt a b = true ↔ (a : Int) < (b : Int) := by
  simp [slt]

theorem sgt_iff (a b : Int256) : sgt a b = true ↔ (a : Int) > (b : Int) := by
  simp [sgt]

theorem sle_iff (a b : Int256) : sle a b = true ↔ (a : Int) ≤ (b : Int) := by
  simp [sle]

theorem sge_iff (a b : Int256) : sge a b = true ↔ (a : Int) ≥ (b : Int) := by
  simp [sge]

theorem isNeg_eq (value : Int256) :
    isNeg value = decide (signBit ≤ value.word.val) := rfl


section Examples

example : (((Int256.ofUint256 (Uint256.ofNat (modulus - 1)) : Int256) : Int)) = -1 := by
  native_decide

example : (((Int256.ofUint256 (Uint256.ofNat signBit) : Int256) : Int)) = minValue := by
  native_decide

example : (Int256.ofInt (-1)).toUint256 = Uint256.ofNat (modulus - 1) := by
  native_decide

example : (Int256.ofInt minValue).toUint256 = Uint256.ofNat signBit := by
  native_decide

example : (-(Int256.ofInt minValue) : Int256) = Int256.ofInt minValue := by
  native_decide

example : (Int256.ofInt (-7) / Int256.ofInt 3 : Int256) = Int256.ofInt (-2) := by
  native_decide

example : (Int256.ofInt 7 / Int256.ofInt (-3) : Int256) = Int256.ofInt (-2) := by
  native_decide

example : (Int256.ofInt (-7) % Int256.ofInt 3 : Int256) = Int256.ofInt (-1) := by
  native_decide

example : (Int256.ofInt 7 % Int256.ofInt (-3) : Int256) = Int256.ofInt 1 := by
  native_decide

example : (Int256.ofInt (-7) / (0 : Int256) : Int256) = 0 := by
  native_decide

example : (Int256.ofInt (-7) % (0 : Int256) : Int256) = 0 := by
  native_decide

example : (Int256.ofInt minValue / Int256.ofInt (-1) : Int256) = Int256.ofInt minValue := by
  native_decide

example : (Int256.ofInt maxValue + 1 : Int256) = Int256.ofInt minValue := by
  native_decide

end Examples

end Int256

namespace Uint256

/-- Bit-reinterpretation as `Int256`. The high bit is the sign; there is no
    range check. This matches Solidity's `int256(uint256(x))` cast. -/
def toInt256 (value : Uint256) : Int256 := Int256.ofUint256 value

@[simp] theorem toInt256_ofUint256 (value : Uint256) :
    toInt256 value = Int256.ofUint256 value := rfl

@[simp] theorem toUint256_toInt256 (value : Uint256) :
    (toInt256 value).toUint256 = value := rfl

end Uint256

namespace Int256

/-- Bit-reinterpretation as `Uint256`. There is no range check. This matches
    Solidity's `uint256(int256(x))` cast. -/
theorem toUint256_bit_reinterpret (value : Int256) :
    toUint256 value = value.word := rfl

@[simp] theorem ofUint256_toInt256 (value : Uint256) :
    ofUint256 (Uint256.toInt256 value).toUint256 = ofUint256 value := rfl

end Int256

end Verity.Core
