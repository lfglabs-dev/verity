/-
  Math Safety Library

  This module provides checked arithmetic operations that prevent
  overflow and underflow issues. Operations return Option types
  to signal when bounds are exceeded.

  Philosophy: Optional safety - examples can choose between fast
  unchecked arithmetic (+ and -) or safe checked operations.
-/

import Verity.Core

namespace Verity.Stdlib.Math

open Verity

-- Maximum value for Uint256 (2^256 - 1)
-- Alias of Verity.Core.MAX_UINT256 for backwards compatibility.
abbrev MAX_UINT256 : Nat := Core.MAX_UINT256

-- Safe addition: returns None on overflow
def safeAdd (a b : Uint256) : Option Uint256 :=
  let sum := (a : Nat) + (b : Nat)
  if sum > MAX_UINT256 then
    none
  else
    some (a + b)

-- Safe subtraction: returns None on underflow
def safeSub (a b : Uint256) : Option Uint256 :=
  if (b : Nat) > (a : Nat) then
    none
  else
    some (a - b)

-- Safe multiplication: returns None on overflow
def safeMul (a b : Uint256) : Option Uint256 :=
  let prod := (a : Nat) * (b : Nat)
  if prod > MAX_UINT256 then
    none
  else
    some (a * b)

-- Safe division: returns None if divisor is zero
def safeDiv (a b : Uint256) : Option Uint256 :=
  if b.val = 0 then
    none
  else
    some (a / b)

/-- Fixed-point scaling factor used by `wMulDown` and `wDivUp`. -/
def WAD : Uint256 := 1000000000000000000

/-- Natural-number form of the wad scale for fixed-point reference code. -/
def WAD_NAT : Nat := 1000000000000000000

/-- BN254 scalar field modulus used by Groth16/BN254 circuit public inputs. -/
def SNARK_SCALAR_FIELD : Uint256 :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Reduce a word modulo the BN254 scalar field. -/
def modField (x : Uint256) : Uint256 :=
  Verity.Core.Uint256.mod x SNARK_SCALAR_FIELD

/-- Count leading zero bits in a 256-bit word. This is the executable
    counterpart of the compiler's `clz` contract-expression sugar. -/
def clz (x : Uint256) : Uint256 :=
  Verity.Core.Uint256.ofNat (if x.val = 0 then 256 else 255 - Nat.log2 x.val)

/-- Most-significant set-bit index, returning `0` for `0`. -/
def msb (x : Uint256) : Uint256 :=
  if x.val = 0 then 0 else Verity.Core.Uint256.ofNat (255 - (clz x).val)

/-- `mulDivDown(a, b, c)` = `floor(a * b / c)` under the EVM's `div` semantics. -/
def mulDivDown (a b c : Uint256) : Uint256 :=
  (a * b) / c

/-- `mulDivUp(a, b, c)` = `ceil(a * b / c)` when the numerator fits without wrapping. -/
def mulDivUp (a b c : Uint256) : Uint256 :=
  ((a * b) + (c - 1)) / c

/-- Full-precision floor multiply-divide.

Unlike `mulDivDown`, this computes the product in unbounded natural-number
precision and returns `none` only when the divisor is zero or the final quotient
does not fit in `uint256`. This matches the proof shape needed for Solidity
`Math.mulDiv(..., Rounding.Floor)` / `FullMath.mulDiv` modeling without adding
an artificial no-overflow hypothesis on `a * b`. -/
def mulDiv512Down? (a b c : Uint256) : Option Uint256 :=
  if (c : Nat) = 0 then
    none
  else
    let q := ((a : Nat) * (b : Nat)) / (c : Nat)
    if q > MAX_UINT256 then none else some (Core.Uint256.ofNat q)

/-- Full-precision ceil multiply-divide.

The product is computed in unbounded natural-number precision. The helper
returns `none` when the divisor is zero or the rounded-up quotient does not fit
in `uint256`. -/
def mulDiv512Up? (a b c : Uint256) : Option Uint256 :=
  if (c : Nat) = 0 then
    none
  else
    let q := (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)
    if q > MAX_UINT256 then none else some (Core.Uint256.ofNat q)

/-- `mulDiv512Down(a, b, c)` = full-precision `floor((a * b) / c)`,
    matching the IR's revert-on-overflow Yul helper. The Lean def
    short-circuits on the failure boundary by returning `0`; the
    proof surface `mulDiv512Down?` (`Option Uint256`) is the
    correctness witness when the quotient fits. (verity#1761) -/
def mulDiv512Down (a b c : Uint256) : Uint256 :=
  match mulDiv512Down? a b c with
  | some r => r
  | none => 0

/-- `mulDiv512Up(a, b, c)` = full-precision `ceil((a * b) / c)`,
    matching the IR's revert-on-overflow Yul helper.  Defined
    analogously to `mulDiv512Down` via `mulDiv512Up?`. (verity#1761) -/
def mulDiv512Up (a b c : Uint256) : Uint256 :=
  match mulDiv512Up? a b c with
  | some r => r
  | none => 0

/-- `ceilDiv(a, b)` = `ceil(a / b)`, matching Solidity's Math256.ceilDiv / OpenZeppelin.
    Uses the overflow-safe formula: `a == 0 ? 0 : (a - 1) / b + 1`.
    Note: When `b = 0` and `a > 0`, EVM `DIV` returns 0, so this yields 1.
    Solidity ≥0.8 reverts on `/0` at the compiler level; that revert is modeled
    at the contract level, not here. -/
def ceilDiv (a b : Uint256) : Uint256 :=
  if a == 0 then 0
  else (a - 1) / b + 1

@[simp] theorem ceilDiv_def (a b : Uint256) :
  ceilDiv a b = if a == 0 then 0 else (a - 1) / b + 1 := rfl

/-- Multiply two wad-scaled values and round down. -/
def wMulDown (a b : Uint256) : Uint256 :=
  mulDivDown a b WAD

/-- Divide two wad-scaled values and round up. -/
def wDivUp (a b : Uint256) : Uint256 :=
  mulDivUp a WAD b

/-! ### TickLib fixed-point exponential reference (verity#1998)

`tickToPrice` in the downstream Morpho Midnight port currently lowers through a
trusted Yul ECM.  The definitions below expose the `wExp` approximation used by
that ECM as ordinary Lean/Verity source: range reduction by `ln 2`, a cubic
wad-scaled Taylor kernel for the residual, binary scaling by `2^q`, and
reciprocal inversion for negative inputs.

The reference intentionally keeps unbounded `Nat`/`Int` arithmetic at this layer
so proofs can state the mathematical shape independently of EVM wrapping. -/

/-- Wad-scaled `ln 2` constant used by the TickLib `wExp` reference. -/
def WEXP_LN2 : Nat := 693147180559945309

/-- Rounding offset used before dividing by `ln 2` in TickLib `wExp`. -/
def WEXP_RANGE_OFFSET : Nat := 322611214989459870

/-- Wad-scaled `1e36`, used for reciprocal inversion of negative exponents. -/
def WEXP_ONE_E36 : Nat := 1000000000000000000000000000000000000

/-- Wad-scaled `ln(1 + delta)` constant used by Morpho Midnight TickLib. -/
def WEXP_TICK_LN_ONE_PLUS_DELTA : Nat := 4987541511039073

/-- Half of the maximum supported Midnight tick. -/
def WEXP_MAX_TICK_HALF : Nat := 2910

/-- Final TickLib price rounding quantum. -/
def WEXP_PRICE_ROUNDING_STEP : Nat := 1000000000000

/-- TickLib's cubic residual approximation for `exp(r / 1e18)`, wad-scaled.

For a nonnegative residual `r`, this is
`1e18 + r + floor(r^2 / (2 * 1e18)) +
 floor(floor(r^2 / (2 * 1e18)) * r / (3 * 1e18))`. -/
def wExpCubicKernel (r : Nat) : Nat :=
  let second := (r * r) / (2 * WAD_NAT)
  let third := (second * r) / (3 * WAD_NAT)
  WAD_NAT + r + second + third

/-- Signed division matching EVM `sdiv`: quotient truncates toward zero. -/
def sdivTrunc (a b : Int) : Int :=
  if b = 0 then
    0
  else if a < 0 then
    -Int.ofNat (Int.natAbs a / Int.natAbs b)
  else
    Int.ofNat (Int.toNat a / Int.natAbs b)

/-- Signed cubic residual approximation used after TickLib range reduction. -/
def wExpSignedCubicKernel (r : Int) : Int :=
  let second := sdivTrunc (r * r) (2 * Int.ofNat WAD_NAT)
  let third := sdivTrunc (second * r) (3 * Int.ofNat WAD_NAT)
  Int.ofNat WAD_NAT + r + second + third

/-- Absolute value as a natural number for TickLib `wExp` inputs. -/
def wExpAbsInput (x : Int) : Nat :=
  if x < 0 then Int.natAbs x else Int.toNat x

/-- TickLib range-reduction quotient, rounded with `WEXP_RANGE_OFFSET`. -/
def wExpRangeQ (xAbs : Nat) : Nat :=
  (xAbs + WEXP_RANGE_OFFSET) / WEXP_LN2

/-- TickLib signed residual after range reduction by `ln 2`. -/
def wExpRangeR (xAbs : Nat) : Int :=
  Int.ofNat xAbs - Int.ofNat (wExpRangeQ xAbs * WEXP_LN2)

/-- Lean reference for the TickLib wad exponential approximation.

This mirrors the downstream ECM's `wExp` block: approximate the range-reduced
residual with `wExpSignedCubicKernel`, scale by `2^q`, and invert around `1e36`
for negative inputs. -/
def tickWExpReference (x : Int) : Nat :=
  let xAbs := wExpAbsInput x
  let q := wExpRangeQ xAbs
  let r := wExpRangeR xAbs
  let scaled := Int.toNat (wExpSignedCubicKernel r) * (2 ^ q)
  if x < 0 then WEXP_ONE_E36 / scaled else scaled

/-- Lean reference for the Morpho Midnight `TickLib.tickToPrice` ECM. -/
def tickToPriceReference (tick : Nat) : Nat :=
  let x := Int.ofNat WEXP_TICK_LN_ONE_PLUS_DELTA *
    (Int.ofNat WEXP_MAX_TICK_HALF - Int.ofNat tick)
  let wexp := tickWExpReference x
  let den := WAD_NAT + wexp
  let raw := (WEXP_ONE_E36 + (den - 1) / 2) / den
  ((raw + (WEXP_PRICE_ROUNDING_STEP - 1) / 2) / WEXP_PRICE_ROUNDING_STEP) *
    WEXP_PRICE_ROUNDING_STEP

-- Helper: Require with Option - fails if None
-- For Uint256 specifically (can be generalized later if needed)
def requireSomeUint (opt : Option Uint256) (message : String) : Contract Uint256 := do
  match opt with
  | some value => return value
  | none => do
    require false message
    -- This line is unreachable in real execution (require would revert)
    -- Return 0 as a fallback for type checking
    return 0

/-! ### Solidity-0.8 default-revert arithmetic (verity#1752)

These wrappers expose the same semantics as Solidity 0.8's `a + b` / `a - b` /
`a * b` / `a / b` on `uint256`, where overflow / underflow / division-by-zero
reverts with `Panic(0x11)` / `Panic(0x12)` rather than wrapping mod `2^256`.

They are thin compositions of `safeAdd` / `safeSub` / `safeMul` / `safeDiv` with
`requireSomeUint`, recognised by the `verity_contract` macro as ergonomic bind
sources so contract authors can write the Solidity-faithful form on one line:

```lean
let total ← addPanic total amount
```

instead of the visually divergent

```lean
let total ← requireSomeUint (safeAdd total amount) "Overflow"
```

The macro lowers `let x ← addPanic a b` directly to the same IR as
`let x ← requireSomeUint (safeAdd a b) "Panic(0x11): arithmetic overflow"`. -/

/-- `a + b` on `Uint256` with Solidity-0.8 panic-on-overflow semantics. -/
def addPanic (a b : Uint256) : Contract Uint256 :=
  requireSomeUint (safeAdd a b) "Panic(0x11): arithmetic overflow"

/-- `a - b` on `Uint256` with Solidity-0.8 panic-on-underflow semantics. -/
def subPanic (a b : Uint256) : Contract Uint256 :=
  requireSomeUint (safeSub a b) "Panic(0x11): arithmetic underflow"

/-- `a * b` on `Uint256` with Solidity-0.8 panic-on-overflow semantics. -/
def mulPanic (a b : Uint256) : Contract Uint256 :=
  requireSomeUint (safeMul a b) "Panic(0x11): arithmetic overflow"

/-- `a / b` on `Uint256` with Solidity-0.8 panic-on-division-by-zero semantics. -/
def divPanic (a b : Uint256) : Contract Uint256 :=
  requireSomeUint (safeDiv a b) "Panic(0x12): division by zero"

-- Full-result simp lemmas for requireSomeUint
@[simp] theorem requireSomeUint_some (v : Uint256) (msg : String) (s : ContractState) :
  (requireSomeUint (some v) msg).run s = ContractResult.success v s := rfl

@[simp] theorem requireSomeUint_none (msg : String) (s : ContractState) :
  (requireSomeUint none msg).run s = ContractResult.revert msg s := rfl

@[simp] theorem WAD_val : (WAD : Nat) = 1000000000000000000 := by
  rfl

@[simp] theorem WAD_NAT_val : WAD_NAT = 1000000000000000000 := by
  rfl

@[simp] theorem SNARK_SCALAR_FIELD_val :
    (SNARK_SCALAR_FIELD : Nat) =
      21888242871839275222246405745257275088548364400416034343698204186575808495617 := by
  rfl

@[simp] theorem modField_def (x : Uint256) :
    modField x = Verity.Core.Uint256.mod x SNARK_SCALAR_FIELD := rfl

theorem WAD_ne_zero : WAD ≠ 0 := by
  intro h
  have : ((WAD : Uint256) : Nat) = 0 := by
    simpa using congrArg (fun x : Uint256 => (x : Nat)) h
  have hPos : 0 < (1000000000000000000 : Nat) := by decide
  simp [WAD] at this
  exact (Nat.ne_of_gt hPos) this

@[simp] theorem mulDivDown_def (a b c : Uint256) :
  mulDivDown a b c = (a * b) / c := rfl

@[simp] theorem mulDivUp_def (a b c : Uint256) :
  mulDivUp a b c = ((a * b) + (c - 1)) / c := rfl

@[simp] theorem mulDiv512Down?_def (a b c : Uint256) :
  mulDiv512Down? a b c =
    if (c : Nat) = 0 then
      none
    else
      let q := ((a : Nat) * (b : Nat)) / (c : Nat)
      if q > MAX_UINT256 then none else some (Core.Uint256.ofNat q) := by
  unfold mulDiv512Down?
  split <;> rfl

@[simp] theorem mulDiv512Up?_def (a b c : Uint256) :
  mulDiv512Up? a b c =
    if (c : Nat) = 0 then
      none
    else
      let q := (((a : Nat) * (b : Nat)) + ((c : Nat) - 1)) / (c : Nat)
      if q > MAX_UINT256 then none else some (Core.Uint256.ofNat q) := by
  unfold mulDiv512Up?
  split <;> rfl

@[simp] theorem wMulDown_def (a b : Uint256) :
  wMulDown a b = mulDivDown a b WAD := rfl

@[simp] theorem wDivUp_def (a b : Uint256) :
  wDivUp a b = mulDivUp a WAD b := rfl

end Verity.Stdlib.Math
