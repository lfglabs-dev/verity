import Contracts.Smoke.Storage

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

verity_contract CustomErrorSmoke where
  storage
    sentinel : Uint256 := slot 0

  errors
    error NonPositive(Uint256)
    error AmountTooLarge(Uint256, Uint256)

  function echo (amount : Uint256) : Uint256 := do
    return amount

verity_contract SafeMulRequireSmoke where
  storage
    product : Uint256 := slot 0

  function multiplyStored (factor : Uint256) : Uint256 := do
    let current ← getStorage product
    let next ← requireSomeUint (safeMul current factor) "Product overflow"
    setStorage product next
    return next

  function divideStored (divisor : Uint256) : Uint256 := do
    let current ← getStorage product
    let next ← requireSomeUint (safeDiv current divisor) "Division by zero"
    setStorage product next
    return next

-- Solidity-0.8 default-revert arithmetic (verity#1752).
--
-- `addPanic` / `subPanic` / `mulPanic` / `divPanic` are ergonomic bind
-- sources that model the Solidity 0.8 default semantics for `a + b`,
-- `a - b`, `a * b`, `a / b` on `uint256`: revert with `Panic(0x11)` on
-- overflow / underflow and `Panic(0x12)` on division by zero, rather
-- than wrapping mod `2^256`. They desugar to the same IR as
-- `let x ← requireSomeUint (safeXxx a b) "<fixed message>"`, which
-- collapses the visual divergence from the Solidity source while
-- still reverting on the same boundary conditions.
verity_contract ArithmeticPanicSmoke where
  storage
    balance : Uint256 := slot 0

  function deposit (amount : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← addPanic current amount
    setStorage balance next
    return next

  function withdraw (amount : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← subPanic current amount
    setStorage balance next
    return next

  function scaleStored (factor : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← mulPanic current factor
    setStorage balance next
    return next

  function shareStored (divisor : Uint256) : Uint256 := do
    let current ← getStorage balance
    let next ← divPanic current divisor
    setStorage balance next
    return next

-- Full-precision multiply-divide (verity#1761).
--
-- `mulDiv512Down(a, b, c)` and `mulDiv512Up(a, b, c)` compile to a Yul
-- helper that performs `floor((a * b) / c)` / `ceil((a * b) / c)` at
-- 512-bit precision using the OpenZeppelin/Solmate `FullMath.mulDiv`
-- algorithm. They revert on division by zero and on quotient overflow.
-- Unlike `mulDivDown` / `mulDivUp` (which compile to `div(mul(a, b), c)`
-- and require the intermediate product to fit in 256 bits), the
-- 512-bit variants handle the full Solidity `Math.mulDiv` semantics
-- needed by Cork Phoenix and other DeFi math.
verity_contract MulDiv512Smoke where
  storage
    lastFloor : Uint256 := slot 0
    lastCeil  : Uint256 := slot 1

  function storeFloor (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
    let q := mulDiv512Down a b c
    setStorage lastFloor q
    return q

  function storeCeil (a : Uint256, b : Uint256, c : Uint256) : Uint256 := do
    let q := mulDiv512Up a b c
    setStorage lastCeil q
    return q

verity_contract ByteBuiltinSmoke where
  storage
    extracted : Uint256 := slot 0

  constants
    highByte : Uint256 := (byte 0 (shl 248 0xab))
    middleByte : Uint256 := (byte 15 (shl 128 0xcd))
    lowByte : Uint256 := (byte 31 0xff)
    outOfBoundsByte : Uint256 := (byte 32 0xff)

  function extract (index : Uint256, word : Uint256) : Uint256 := do
    return (byte index word)

  function highByteConstant () : Uint256 := do
    return highByte

  function lowByteConstant () : Uint256 := do
    return lowByte

  function middleByteConstant () : Uint256 := do
    return middleByte

  function outOfBoundsByteConstant () : Uint256 := do
    return outOfBoundsByte

  function storeExtracted (index : Uint256, word : Uint256) : Uint256 := do
    let result := byte index word
    setStorage extracted result
    return result

example :
    ByteBuiltinSmoke.extract_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.byte
            (Compiler.CompilationModel.Expr.param "index")
            (Compiler.CompilationModel.Expr.param "word"))
      ] := rfl

example :
    ByteBuiltinSmoke.storeExtracted_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar
          "result"
          (Compiler.CompilationModel.Expr.byte
            (Compiler.CompilationModel.Expr.param "index")
            (Compiler.CompilationModel.Expr.param "word"))
      , Compiler.CompilationModel.Stmt.setStorage
          "extracted"
          (Compiler.CompilationModel.Expr.localVar "result")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "result")
      ] := rfl

def byteBuiltinExecutableExtractsHighByte : Bool :=
  match ByteBuiltinSmoke.extract 0 (shl 248 0xab) Verity.defaultState with
  | .success result state =>
      result == (0xab : Uint256) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : byteBuiltinExecutableExtractsHighByte = true := by decide

def byteBuiltinExecutableExtractsMiddleByte : Bool :=
  match ByteBuiltinSmoke.extract 15 (shl 128 0xcd) Verity.defaultState with
  | .success result state =>
      result == (0xcd : Uint256) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : byteBuiltinExecutableExtractsMiddleByte = true := by decide

def byteBuiltinExecutableExtractsLowByte : Bool :=
  match ByteBuiltinSmoke.extract 31 (0xff : Uint256) Verity.defaultState with
  | .success result state =>
      result == (0xff : Uint256) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : byteBuiltinExecutableExtractsLowByte = true := by decide

def byteBuiltinExecutableZeroesOutOfBoundsIndex : Bool :=
  match ByteBuiltinSmoke.extract 32 (0xff : Uint256) Verity.defaultState with
  | .success result state =>
      result == (0 : Uint256) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : byteBuiltinExecutableZeroesOutOfBoundsIndex = true := by decide

def byteBuiltinExecutableZeroesMaxIndex : Bool :=
  match ByteBuiltinSmoke.extract (Verity.Core.MAX_UINT256 : Uint256) (0xff : Uint256) Verity.defaultState with
  | .success result state =>
      result == (0 : Uint256) && state.sender == Verity.defaultState.sender
  | .revert _ _ => false

example : byteBuiltinExecutableZeroesMaxIndex = true := by decide

def byteBuiltinConstantsUseByteSemantics : Bool :=
  match ByteBuiltinSmoke.highByteConstant Verity.defaultState,
      ByteBuiltinSmoke.middleByteConstant Verity.defaultState,
      ByteBuiltinSmoke.lowByteConstant Verity.defaultState,
      ByteBuiltinSmoke.outOfBoundsByteConstant Verity.defaultState with
  | .success high _, .success middle _, .success low _, .success outOfBounds _ =>
      high == (0xab : Uint256) &&
      middle == (0xcd : Uint256) &&
      low == (0xff : Uint256) &&
      outOfBounds == (0 : Uint256)
  | _, _, _, _ => false

example : byteBuiltinConstantsUseByteSemantics = true := by decide

def byteBuiltinExecutableStoresExtractedByte : Bool :=
  match ByteBuiltinSmoke.storeExtracted 31 (0xff : Uint256) Verity.defaultState with
  | .success result state =>
      result == (0xff : Uint256) && state.storage 0 == (0xff : Uint256)
  | .revert _ _ => false

example : byteBuiltinExecutableStoresExtractedByte = true := by decide

verity_contract SignedBuiltinSmoke where
  storage
    signedSlot : Int256 := slot 0

  constants
    extendedByte : Uint256 := (signextend 0 255)
    arithmeticShifted : Uint256 := (sar 255 (sub 0 1))
    negativeOne : Int256 := (toInt256 (sub 0 1))

  function signedDiv (lhs : Uint256, rhs : Uint256) : Uint256 := do
    return (sdiv lhs rhs)

  function signedMod (lhs : Uint256, rhs : Uint256) : Uint256 := do
    return (smod lhs rhs)

  function signedLt (lhs : Uint256, rhs : Uint256) : Bool := do
    return (slt lhs rhs)

  function signedGt (lhs : Uint256, rhs : Uint256) : Bool := do
    return (sgt lhs rhs)

  function arithmeticShift (shift : Uint256, value : Uint256) : Uint256 := do
    return (sar shift value)

  function signExtended () : Uint256 := do
    return extendedByte

  function shiftedMask () : Uint256 := do
    return arithmeticShifted

  function signedDivSurface (lhs : Int256, rhs : Int256) : Int256 := do
    return (lhs / rhs)

  function signedModSurface (lhs : Int256, rhs : Int256) : Int256 := do
    return (lhs % rhs)

  function signedDivViaLocal (raw : Uint256, denom : Int256) : Int256 := do
    let signedRaw := toInt256 raw
    return (signedRaw / denom)

  function castToInt (value : Uint256) : Int256 := do
    return (toInt256 value)

  function castToUint (value : Int256) : Uint256 := do
    return (toUint256 value)

  function minusOne () : Int256 := do
    return negativeOne

  function bitAndSignBit (lhs : Int256, rhs : Int256) : Bool := do
    return (bitAnd lhs rhs < 0)

  function minSignBit (lhs : Int256) : Bool := do
    return (min lhs 0 < 0)

  function storeSigned (value : Int256) : Int256 := do
    setStorage signedSlot value
    let saved ← getStorage signedSlot
    return saved

  function loadSigned () : Int256 := do
    let saved ← getStorage signedSlot
    return saved

end Contracts.Smoke
