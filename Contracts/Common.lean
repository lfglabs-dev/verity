import Compiler.CompilationModel
import Compiler.Proofs.MappingSlot
import Verity.Core
import Verity.Core.Semantics
import Verity.Core.Model.ContractExternalCall
import Verity.EVM.Uint256
import Verity.Macro
import Verity.Stdlib.Math

namespace Contracts

abbrev UIntN := Verity.UIntN
abbrev IntN := Verity.IntN
abbrev BytesN := Verity.BytesN
abbrev Uint24 := Verity.UIntN 24
abbrev Uint32 := Verity.UIntN 32
abbrev Uint40 := Verity.UIntN 40
abbrev Uint48 := Verity.UIntN 48
abbrev Uint56 := Verity.UIntN 56
abbrev Uint64 := Verity.UIntN 64
abbrev Uint72 := Verity.UIntN 72
abbrev Uint80 := Verity.UIntN 80
abbrev Uint88 := Verity.UIntN 88
abbrev Uint96 := Verity.UIntN 96
abbrev Uint104 := Verity.UIntN 104
abbrev Uint112 := Verity.UIntN 112
abbrev Uint120 := Verity.UIntN 120
abbrev Uint128 := Verity.UIntN 128
abbrev Uint136 := Verity.UIntN 136
abbrev Uint144 := Verity.UIntN 144
abbrev Uint152 := Verity.UIntN 152
abbrev Uint160 := Verity.UIntN 160
abbrev Uint168 := Verity.UIntN 168
abbrev Uint176 := Verity.UIntN 176
abbrev Uint184 := Verity.UIntN 184
abbrev Uint192 := Verity.UIntN 192
abbrev Uint200 := Verity.UIntN 200
abbrev Uint208 := Verity.UIntN 208
abbrev Uint216 := Verity.UIntN 216
abbrev Uint224 := Verity.UIntN 224
abbrev Uint232 := Verity.UIntN 232
abbrev Uint240 := Verity.UIntN 240
abbrev Uint248 := Verity.UIntN 248
abbrev Int8 := Verity.IntN 8
abbrev Int16 := Verity.IntN 16
abbrev Int24 := Verity.IntN 24
abbrev Int32 := Verity.IntN 32
abbrev Int40 := Verity.IntN 40
abbrev Int48 := Verity.IntN 48
abbrev Int56 := Verity.IntN 56
abbrev Int64 := Verity.IntN 64
abbrev Int72 := Verity.IntN 72
abbrev Int80 := Verity.IntN 80
abbrev Int88 := Verity.IntN 88
abbrev Int96 := Verity.IntN 96
abbrev Int104 := Verity.IntN 104
abbrev Int112 := Verity.IntN 112
abbrev Int120 := Verity.IntN 120
abbrev Int128 := Verity.IntN 128
abbrev Int136 := Verity.IntN 136
abbrev Int144 := Verity.IntN 144
abbrev Int152 := Verity.IntN 152
abbrev Int160 := Verity.IntN 160
abbrev Int168 := Verity.IntN 168
abbrev Int176 := Verity.IntN 176
abbrev Int184 := Verity.IntN 184
abbrev Int192 := Verity.IntN 192
abbrev Int200 := Verity.IntN 200
abbrev Int208 := Verity.IntN 208
abbrev Int216 := Verity.IntN 216
abbrev Int224 := Verity.IntN 224
abbrev Int232 := Verity.IntN 232
abbrev Int240 := Verity.IntN 240
abbrev Int248 := Verity.IntN 248
abbrev Bytes1 := Verity.BytesN 1
abbrev Bytes2 := Verity.BytesN 2
abbrev Bytes3 := Verity.BytesN 3
abbrev Bytes4 := Verity.BytesN 4
abbrev Bytes5 := Verity.BytesN 5
abbrev Bytes6 := Verity.BytesN 6
abbrev Bytes7 := Verity.BytesN 7
abbrev Bytes8 := Verity.BytesN 8
abbrev Bytes9 := Verity.BytesN 9
abbrev Bytes10 := Verity.BytesN 10
abbrev Bytes11 := Verity.BytesN 11
abbrev Bytes12 := Verity.BytesN 12
abbrev Bytes13 := Verity.BytesN 13
abbrev Bytes14 := Verity.BytesN 14
abbrev Bytes15 := Verity.BytesN 15
abbrev Bytes16 := Verity.BytesN 16
abbrev Bytes17 := Verity.BytesN 17
abbrev Bytes18 := Verity.BytesN 18
abbrev Bytes19 := Verity.BytesN 19
abbrev Bytes20 := Verity.BytesN 20
abbrev Bytes21 := Verity.BytesN 21
abbrev Bytes22 := Verity.BytesN 22
abbrev Bytes23 := Verity.BytesN 23
abbrev Bytes24 := Verity.BytesN 24
abbrev Bytes25 := Verity.BytesN 25
abbrev Bytes26 := Verity.BytesN 26
abbrev Bytes27 := Verity.BytesN 27
abbrev Bytes28 := Verity.BytesN 28
abbrev Bytes29 := Verity.BytesN 29
abbrev Bytes30 := Verity.BytesN 30
abbrev Bytes31 := Verity.BytesN 31

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

macro_rules
  | `(doElem| let _ := externalCall $name:ident [ $[$args:term],* ]) => do
      let fresh ← Lean.Macro.addMacroScope `_callResult
      let freshIdent := Lean.mkIdent fresh
      `(doElem| let $freshIdent : Uint256 := externalCall $name [ $[$args],* ])
  | `(doElem| let _ := externalCall $name:str [ $[$args:term],* ]) => do
      let fresh ← Lean.Macro.addMacroScope `_callResult
      let freshIdent := Lean.mkIdent fresh
      `(doElem| let $freshIdent : Uint256 := externalCall $name [ $[$args],* ])
  -- DSL ergonomics: rewrite `let _ := rhs` into a do-block-friendly form
  -- so that consumers can discard an external-call result naturally.
  -- (Without this rule the verity_contract function-body parser rejects
  -- `let _ := …` as an unsupported do element.)
  | `(doElem| let _ := $rhs:term) => do
      let fresh ← Lean.Macro.addMacroScope `_callResult
      let freshIdent := Lean.mkIdent fresh
      `(doElem| let $freshIdent := $rhs)
  | `(term| ecmCall $_moduleFactory:term $_args:term) =>
      `(term| do
          let _ := $_moduleFactory
          pure (0 : Uint256))
  | `(term| ecmDo $_module:term $_args:term) =>
      `(term| do
          let _ := $_module
          pure ())
  | `(doElem| ecmBind [ $[$names:ident],* ] $_module:term $_args:term) =>
      `(doElem| do
          let _ := $_module
          $[let $names := (0 : Uint256)]*
          pure ())
  | `(doElem| unsafe $_reason:str do $body:doSeq) =>
      `(doElem| do $body)
  | `(doElem| tryCatch $attempt:term (fun $name:ident => do $[$elems:doElem]*)) => do
      let tryCatchFn := Lean.mkIdentFrom attempt `_root_.Contracts.tryCatchWord
      `(doElem| $tryCatchFn:ident $attempt (fun $name => do $[$elems:doElem]*))
  | `(doElem| tryCatch $attempt:term (do $[$elems:doElem]*)) => do
      let tryCatchFn := Lean.mkIdentFrom attempt `_root_.Contracts.tryCatchWord
      `(doElem| $tryCatchFn:ident $attempt (fun _ => do $[$elems:doElem]*))
  | `(doElem| revert $errorName:ident($args,*)) => do
      let revertFn := Lean.mkIdentFrom errorName `_root_.Contracts.revertCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $revertFn:ident
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| revertError $errorName:ident($args,*)) => do
      let revertFn := Lean.mkIdentFrom errorName `_root_.Contracts.revertCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $revertFn:ident
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| requireError $cond:term $errorName:ident($args,*)) => do
      let requireFn := Lean.mkIdentFrom errorName `_root_.Contracts.requireCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `(doElem| $requireFn:ident
          $cond
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| panic($code:term)) => do
      let panicFn := Lean.mkIdentFrom code `_root_.Contracts.revertPanicAs
      `(doElem| $panicFn:ident $code)
  | `(requireSomeUintError $optExpr:term $errorName:ident($args,*)) => do
      let requireFn := Lean.mkIdentFrom errorName `_root_.Contracts.requireSomeUintCustomError
      let encodeFn := Lean.mkIdentFrom errorName `_root_.Contracts.CustomErrorArg.encode
      let encodedArgs ← args.getElems.mapM fun arg => `(term| $encodeFn:ident $arg)
      `($requireFn:ident
          $optExpr
          $(Lean.quote (toString errorName.getId))
          [ $[$encodedArgs],* ])
  | `(doElem| let $name:ident := arrayElement $values:term $index:term) => do
      let checked := Lean.mkIdentFrom name `_root_.Contracts.arrayElementChecked
      `(doElem| let $name ← $checked:ident $values $index)
  | `(doElem| let $pat:term := arrayElement $values:term $index:term) => do
      if pat.raw.getKind != `Lean.Parser.Term.tuple then
        Lean.Macro.throwUnsupported
      let checked := Lean.mkIdentFrom values `_root_.Contracts.arrayElementChecked
      `(doElem| let $pat:term ← $checked:ident $values $index)
  | `(doElem| let $name:ident := tload $offset:term) => do
      let load := Lean.mkIdentFrom name `_root_.Contracts.tload
      `(doElem| let $name ← $load:ident $offset)
  | `(doElem| let $pat:term := $rhs:term) => do
      if pat.raw.getKind != `Lean.Parser.Term.tuple then
        Lean.Macro.throwUnsupported
      match rhs.raw with
      | .node _ `Lean.Parser.Term.app args =>
          match args.getD 0 Lean.Syntax.missing with
          | .ident _ raw _ _ =>
              if raw.toString == "structMembers" || raw.toString == "structMembers2" then
                Lean.Macro.throwUnsupported
              else
                `(doElem| let $pat:term ← $rhs:term)
          | _ =>
              Lean.Macro.throwUnsupported
      | _ =>
          Lean.Macro.throwUnsupported


def bitAnd (a b : Uint256) : Uint256 := Verity.Core.Uint256.and a b
def bitOr (a b : Uint256) : Uint256 := Verity.Core.Uint256.or a b
def bitXor (a b : Uint256) : Uint256 := Verity.Core.Uint256.xor a b

abbrev Int256 := Verity.Core.Int256

abbrev toInt256 := Verity.toInt256
abbrev toUint256 := Verity.toUint256

class CustomErrorArg (α : Type) where
  encode : α → String

instance : CustomErrorArg Uint256 where
  encode value := toString (value : Nat)

instance : CustomErrorArg Uint16 where
  encode value := toString value.toNat

instance : CustomErrorArg (UIntN bits) where
  encode value := toString value.toNat

instance : CustomErrorArg (IntN bits) where
  encode value := toString value.toInt

instance : CustomErrorArg (BytesN bytes) where
  encode value := toString value.toNat

instance : CustomErrorArg Nat where
  encode value := toString value

instance : CustomErrorArg Address where
  encode value := toString value.toNat

instance : CustomErrorArg Bool where
  encode value := if value then "true" else "false"

instance : CustomErrorArg String where
  encode value := value

instance : CustomErrorArg ByteArray where
  encode value := reprStr value.toList

instance [CustomErrorArg α] : CustomErrorArg (Array α) where
  encode values := "[" ++ String.intercalate ", " (values.toList.map CustomErrorArg.encode) ++ "]"

instance [CustomErrorArg α] [CustomErrorArg β] : CustomErrorArg (α × β) where
  encode value := "(" ++ CustomErrorArg.encode value.1 ++ ", " ++ CustomErrorArg.encode value.2 ++ ")"

def formatCustomError (name : String) (args : List String) : String :=
  name ++ "(" ++ String.intercalate ", " args ++ ")"

def revertCustomError (name : String) (args : List String) : Contract Unit :=
  require false (formatCustomError name args)

def requireCustomError (condition : Bool) (name : String) (args : List String) : Contract Unit :=
  if condition then pure () else revertCustomError name args

/-- Typed-error counterpart to `Verity.Stdlib.Math.requireSomeUint`. When the
optional value is `some`, the wrapper unwraps it. When `none`, the wrapper
reverts with the supplied custom error name and ABI-style argument list,
matching the revert payload emitted by `requireError`. The runtime helper is
named `requireSomeUintCustomError` rather than `requireSomeUintError` because
the latter is a reserved EDSL keyword (see `Verity/Macro/Syntax.lean`); the
fallback `return 0` is unreachable in real execution because the preceding
revert always returns. -/
def requireSomeUintCustomError (opt : Option Uint256) (name : String) (args : List String) : Contract Uint256 := do
  match opt with
  | some value => return value
  | none => do
    let _ ← revertCustomError name args
    return 0

/-- Solidity-style explicit narrowing conversions. Unsigned and signed casts
keep the low `bits`; fixed-bytes casts interpret the ABI word as left-aligned. -/
def narrowUInt (bits : Nat) (value : Uint256) : UIntN bits :=
  Verity.Core.UIntN.ofUint256 bits value

def narrowInt (bits : Nat) (value : Uint256) : IntN bits :=
  Verity.Core.IntN.ofUint256 bits value

def narrowBytes (bytes : Nat) (value : Uint256) : BytesN bytes :=
  Verity.Core.BytesN.ofUint256 bytes value

/-- Checked narrow arithmetic used by executable models. The macro lowers the
same source forms to width-specific guards before the Yul arithmetic result. -/
def narrowAddPanic {bits : Nat} (a b : UIntN bits) : Contract (UIntN bits) := fun state =>
  if a.val + b.val < 2 ^ bits then
    ContractResult.success (Verity.Core.UIntN.ofNat bits (a.val + b.val)) state
  else
    ContractResult.revert "Panic(0x11): narrow arithmetic overflow" state

def narrowSubPanic {bits : Nat} (a b : UIntN bits) : Contract (UIntN bits) := fun state =>
  if b.val ≤ a.val then
    ContractResult.success (Verity.Core.UIntN.ofNat bits (a.val - b.val)) state
  else
    ContractResult.revert "Panic(0x11): narrow arithmetic underflow" state

def narrowMulPanic {bits : Nat} (a b : UIntN bits) : Contract (UIntN bits) := fun state =>
  if a.val * b.val < 2 ^ bits then
    ContractResult.success (Verity.Core.UIntN.ofNat bits (a.val * b.val)) state
  else
    ContractResult.revert "Panic(0x11): narrow arithmetic overflow" state

/-- Executable counterpart to the `Stmt.panicCode` model/IR surface. Reverts
unconditionally, mirroring Solidity's built-in `Panic(uint256)` payload that the
Yul lowering emits (`solidityPanicPayloadExpr`). The runtime message carries the
decimal panic code; on-chain the compiled contract reverts with the ABI-encoded
`Panic(uint256)` selector + code instead. -/
def revertPanic (code : Uint256) : Contract Unit :=
  revertCustomError "Panic" [CustomErrorArg.encode code]

/-- Polymorphic executable counterpart used when a terminating panic appears in
an expression-valued generated body. Keep `revertPanic`'s public signature
source-compatible for direct callers. -/
def revertPanicAs {α : Type} (code : Uint256) : Contract α :=
  fun state => ContractResult.revert s!"Panic({code.val})" state

private def wordToSigned (value : Uint256) : Int :=
  (toInt256 value : Int)

private def signedToWord (value : Int) : Uint256 :=
  toUint256 (Verity.Core.Int256.ofInt value)

instance : CustomErrorArg Int256 where
  encode value := toString (value : Int)

private def pow2 (n : Nat) : Nat := 2 ^ n

def sdiv (a b : Uint256) : Uint256 :=
  toUint256 (toInt256 a / toInt256 b)

def smod (a b : Uint256) : Uint256 :=
  toUint256 (toInt256 a % toInt256 b)

def slt (a b : Uint256) : Bool := wordToSigned a < wordToSigned b
def sgt (a b : Uint256) : Bool := wordToSigned a > wordToSigned b

def sar (shift value : Uint256) : Uint256 :=
  let shiftNat : Nat := shift
  if shiftNat >= 256 then
    if wordToSigned value < 0 then
      (Verity.Core.MAX_UINT256 : Uint256)
    else
      0
  else
    let divisor := Int.ofNat (pow2 shiftNat)
    signedToWord (Int.ediv (wordToSigned value) divisor)

def byte (index value : Uint256) : Uint256 :=
  Verity.Core.Uint256.byte index value

def signextend (byteIndex value : Uint256) : Uint256 :=
  let idx : Nat := byteIndex
  if idx >= 32 then
    value
  else
    let bitIndex := 8 * idx + 7
    let width := bitIndex + 1
    let lowMask := pow2 width - 1
    let lowBits := (value : Nat) % pow2 width
    let signSet := ((lowBits / pow2 bitIndex) % 2) == 1
    if signSet then
      ((lowBits + (Verity.Core.Uint256.modulus - lowMask - 1)) : Uint256)
    else
      (lowBits : Uint256)

abbrev mulDivDown := Verity.Stdlib.Math.mulDivDown
abbrev mulDivUp := Verity.Stdlib.Math.mulDivUp

abbrev wMulDown := Verity.Stdlib.Math.wMulDown
abbrev wDivUp := Verity.Stdlib.Math.wDivUp

def min (a b : Uint256) : Uint256 := if a <= b then a else b
def max (a b : Uint256) : Uint256 := if a >= b then a else b
def ite (cond : Prop) [Decidable cond] (thenVal elseVal : Uint256) : Uint256 :=
  if cond then thenVal else elseVal
def logicalAnd (a b : Uint256) : Uint256 := if a != 0 && b != 0 then 1 else 0
def logicalOr (a b : Uint256) : Uint256 := if a != 0 || b != 0 then 1 else 0
def logicalNot (a : Uint256) : Uint256 := if a == 0 then 1 else 0
def tryCatchWord (attempt : Uint256) (handler : String → Contract Unit) : Contract Unit :=
  if attempt == 0 then handler "" else pure ()
def calldatasize : Uint256 := 0
def returndataSize : Uint256 := 0
def calldataload (offset : Uint256) : Uint256 := offset
def mload (offset : Uint256) : Uint256 := offset
def tload (offset : Uint256) : Contract Uint256 := fun state =>
  ContractResult.success (state.transientStorage (offset : Nat)) state
def extcodesize (addr : Uint256) : Uint256 := addr
def keccak256 (offset size : Uint256) : Uint256 := add offset size
def call (gas target value inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add value (add inOffset (add inSize (add outOffset outSize)))))
def staticcall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def delegatecall (gas target inOffset inSize outOffset outSize : Uint256) : Uint256 :=
  add gas (add target (add inOffset (add inSize (add outOffset outSize))))
def ecrecover (hash v r sigS : Uint256) : Contract Address := fun state =>
  ContractResult.success
    (wordToAddress ((Verity.Env.ofWorld state).callOracle "ecrecover" [hash, v, r, sigS]))
    state
def calldatacopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def returndataCopy (_destOffset _sourceOffset _size : Uint256) : Contract Unit := pure ()
def revertReturndata : Contract Unit := pure ()
/-- Executable length surface for `arrayLength`: dynamic ABI values that
carry a length word (`bytes`, `string`, `T[]`). Deliberately not
instantiated for word types: `Bytes32` is a reducible abbrev of `Uint256`,
so an instance there would make `arrayLength` typecheck (and return 32)
for arbitrary words. -/
class ArrayLength (α : Type) where
  size : α → Nat
instance : ArrayLength ByteArray where
  size := ByteArray.size
instance : ArrayLength String where
  size := String.utf8ByteSize
instance {α : Type} : ArrayLength (Array α) where
  size := Array.size
def arrayLength {α : Type} [ArrayLength α] (values : α) : Uint256 := ArrayLength.size values
def arrayElement {α : Type} [Inhabited α] (values : Array α) (index : Uint256) : α :=
  values.getD (index : Nat) (Inhabited.default : α)
def abiHeadWord {α : Type} [Inhabited α] (_value : α) (_wordOffset : Uint256) : Uint256 := 0
def abiEncode {α : Type} [Inhabited α] (_value : α) : Uint256 := 0
def arrayElementChecked {α : Type} (values : Array α) (index : Uint256) : Contract α := fun state =>
  if h : (index : Nat) < values.size then
    ContractResult.success (values[(index : Nat)]'h) state
  else
    ContractResult.revert "Array index out of bounds" state
def allocArray (len : Uint256) : Contract (Array Uint256) :=
  pure (Array.replicate (len : Nat) 0)
def setMemoryArrayElement (values : Array Uint256) (index value : Uint256) : Contract Unit :=
  let _ := values
  let _ := index
  let _ := value
  pure ()
def returnArray {α : Type} (values : Array α) : Contract (Array α) := pure values
def returnValues (_values : List Uint256) : Contract Unit := pure ()
def returnBytes {α : Type} (value : α) : Contract α := pure value
def returnStorageWords {α : Type} (_slots : Array α) : Contract (Array Uint256) := pure #[]
def returnCodeData {α : Type} [Inhabited α] (_pointer : Address) : Contract α :=
  pure (Inhabited.default : α)

inductive EventArg where
  | word (value : Contract Uint256)
  | dynamicArray (length : Contract Uint256)

namespace EventArg

def toWord : EventArg → Contract Uint256
  | .word value => value
  | .dynamicArray length => length

end EventArg

instance : Coe Uint256 EventArg where
  coe value := EventArg.word (pure value)

instance : Coe Uint16 EventArg where
  coe value := EventArg.word (pure value.toUint256)

instance : Coe Bool EventArg where
  coe value := EventArg.word (pure (if value then 1 else 0))

instance (α : Type) : CoeTC (Array α) EventArg where
  coe values := EventArg.dynamicArray (pure values.size)

instance (α : Type) : CoeTC (Contract (Array α)) EventArg where
  coe values := EventArg.dynamicArray (do
    let array ← values
    pure array.size)

def emit (name : String) (args : List EventArg) : Contract Unit := do
  let words ← args.mapM EventArg.toWord
  emitEvent name words
def setPackedStorage {α : Type} (rootSlot : StorageSlot α) (wordOffset : Nat)
    (word : Uint256) : Contract Unit := fun state =>
  let targetSlot := (rootSlot.slot + wordOffset) % Compiler.Constants.evmModulus
  ContractResult.success ()
    ((state.writeSlot targetSlot word).writeAddrSlot targetSlot (wordToAddress word))
def rawLog (topics : List Uint256) (dataOffset dataSize : Uint256) : Contract Unit := fun state =>
  if topics.length > 4 then
    ContractResult.revert s!"rawLog supports at most 4 topics, got {topics.length}" state
  else
    ContractResult.success () { state with
      events := state.events ++
        [{ name := s!"log{topics.length}", args := [dataOffset, dataSize], indexedArgs := topics }]
    }
def mstore (_offset _value : Uint256) : Contract Unit := pure ()
def tstore (offset value : Uint256) : Contract Unit := fun state =>
  ContractResult.success () (state.writeTransient (offset : Nat) value)
/-- Canonical journal-word encoding for executable external-call arguments.
Scalars occupy one word. Dynamic values start with their element/byte count
and retain every recursively encoded element, making equal-length content
mutations observable without claiming byte-for-byte EVM ABI layout. -/
class ExternalArg (α : Type) where
  toWords : α → List Uint256
class ExternalResult (α : Type) where
  fromWord : Uint256 → α
/-- Aggregate/no-result executable stubs have no single-word decoding. Keep
their historical inhabited default; concrete scalar decoders below have the
normal higher priority and therefore return the journaled stub word. -/
instance (priority := 100) [Inhabited α] : ExternalResult α where
  fromWord _ := Inhabited.default
instance : ExternalArg Uint256 where
  toWords value := [value]
instance : ExternalArg Uint16 where
  toWords value := [value.toUint256]
instance : ExternalArg (UIntN bits) where
  toWords value := [value.toUint256]
instance : ExternalArg (IntN bits) where
  toWords value := [value.toUint256]
instance : ExternalArg (BytesN bytes) where
  toWords value := [value.toUint256]
instance : ExternalArg Int256 where
  toWords value := [value.word]
instance : ExternalArg Address where
  toWords value := [value.toNat]
instance : ExternalArg Bool where
  toWords value := [if value then 1 else 0]
instance [ExternalArg α] : ExternalArg (Array α) where
  toWords values := values.size :: (values.toList.flatMap ExternalArg.toWords)
instance : ExternalArg ByteArray where
  toWords bytes := bytes.size :: (bytes.data.toList.map (fun byte => (byte.toNat : Uint256)))
instance : ExternalResult Uint256 where
  fromWord value := value
instance : ExternalResult Uint16 where
  fromWord value := Verity.wordToUint16 value
instance : ExternalResult (UIntN bits) where
  fromWord value := Verity.Core.UIntN.ofUint256 bits value
instance : ExternalResult (IntN bits) where
  fromWord value := Verity.Core.IntN.ofUint256 bits value
instance : ExternalResult (BytesN bytes) where
  fromWord value := Verity.Core.BytesN.ofUint256 bytes value
instance : ExternalResult Int256 where
  fromWord value := toInt256 value
instance : ExternalResult Address where
  fromWord value := wordToAddress value
instance : ExternalResult Bool where
  fromWord value := value != 0

namespace Call

/-- First-class external-call result used by executable contract wrappers.
    The compilation-model path lowers `callResult` binds to the same low-level
    try-call wrapper as `tryExternalCall`, while executable tests can inspect
    success and payload as one value. -/
structure Result (α : Type) where
  success : Bool
  returndata : α
  deriving Repr, BEq

namespace Result

def failed (result : Result α) : Bool :=
  !result.success

def payload (result : Result α) : α :=
  result.returndata

end Result

end Call

/-- Deterministic executable stand-in for a linked external call's return
word. Public (not `private`) so specs and tests can state the executable
plane's in-band results and journal entries verbatim. -/
def externalCallStubWord (name : String) (args : List Uint256) : Uint256 :=
  Core.Uint256.ofNat
    (Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stubWord
      name (args.map (fun word => (word : Nat))))

/-- Executable success bit for a linked external call: every linked callee
succeeds except the reserved name `"fail"`, which lets tests exercise the
failure path of `callResult`/`tryExternalCall`. -/
def externalCallStubSuccess (name : String) : Bool :=
  name != "fail"

/-- The journal entry recorded by the EDSL executable plane for one linked
external call. Linked externals are name-keyed (the target address is bound
at link time), so the callee identity lives in `name` and `siteId`/`target`
are zero; the journal position records call order. `calldata` is the exact
argument-word list in call order, so a call with omitted, reordered, or
altered arguments journals a different entry. -/
def linkedCallEntry (name : String) (argWords : List Uint256)
    (control : ExternalCallControl := .success)
    (returndata : List Nat := []) : ExternalCall :=
  { siteId := 0
    kind := .call
    target := 0
    value := 0
    calldata := argWords.map (fun w => (w : Nat))
    control := control
    returndata := returndata
    name := name }

/-- Address- and value-keyed journal entry for the ETH-aware bind. -/
def linkedCallEntryTo (name : String) (target : Address) (value : Uint256)
    (argWords : List Uint256)
    (control : ExternalCallControl := .success)
    (returndata : List Nat := []) : ExternalCall :=
  { linkedCallEntry name argWords control returndata with
    target := target.toNat
    value := value.val }

/-- Model call site corresponding to one executable linked-call crossing. -/
def linkedCallSite (name : String) (argWords : List Uint256)
    (returnArity : Nat := 0) (kind : Compiler.CompilationModel.DenoteExternalCalls.CallKind := .call)
    (target : Nat := 0) (value : Nat := 0) (stubPrefix : List Nat := []) :
    Compiler.CompilationModel.DenoteExternalCalls.CallSite :=
  { siteId := 0, kind, target, value
    calldata := argWords.map (fun word => (word : Nat))
    name, returnArity, stubPrefix, gas := 0 }

/-- Append one entry to the `ContractState.calls` journal. This is the sole
observable-effect primitive of the executable linked-call family; a
subsequent monadic revert rolls the entry back through `Contract.run`'s
snapshot semantics, matching EVM top-level revert observability. -/
def recordLinkedCall (entry : ExternalCall) : Contract Unit := fun state =>
  ContractResult.success () { state with calls := state.calls ++ [entry] }

private abbrev AdversaryModel :=
  Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel
private abbrev ExternalCallResult :=
  Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult
def externalCallResultWord (result : ExternalCallResult) : Uint256 :=
  Core.Uint256.ofNat (result.returndata.head?.getD 0)

/-- PR2 compatibility boundary. The unified model owns call execution and
state evolution; Common temporarily retains its historical live-returndata
projection until the macro default is removed in PR3. -/
def commonExternalCall (adv : AdversaryModel)
    (site : Compiler.CompilationModel.DenoteExternalCalls.CallSite) :
    Contract ExternalCallResult := fun state =>
  match Compiler.CompilationModel.DenoteExternalCalls.externalCall adv site state with
  | .success result post =>
      .success result { post with returndata := state.returndata }
  | .revert message _ => .revert message state

@[simp] theorem commonExternalCall_apply (adv : AdversaryModel)
    (site : Compiler.CompilationModel.DenoteExternalCalls.CallSite)
    (state : ContractState) :
    commonExternalCall adv site state =
      ContractResult.success (adv.result site state)
        { (Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled adv site
            { world := state, gasRemaining := site.gas }).state.world with
          returndata := state.returndata } := rfl

/-- Transitional expression-position boundary. Until PR3 moves macro-expanded
external calls into the caller's `Contract` state, this pure helper can only
soundly execute the deterministic stub adversary. -/
def externalCallWords {α : Type} [ExternalResult α] (name : String) (args : List Uint256)
    (adv : AdversaryModel := .stub) (_hadv : adv = .stub := by rfl) : α :=
  match commonExternalCall adv (linkedCallSite name args 1) defaultState with
  | .success (.success returndata) _ =>
      ExternalResult.fromWord (Core.Uint256.ofNat (returndata.head?.getD 0))
  | .success (.failure _) _ | .success (.revert _) _ =>
      ExternalResult.fromWord (externalCallStubWord name args)
  | .revert _ _ => ExternalResult.fromWord (externalCallStubWord name args)

def callResultWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (adv : AdversaryModel := .stub) : Contract (Call.Result α) := do
  let result ← commonExternalCall adv (linkedCallSite name args 1)
  pure
    { success := result.succeeded
      returndata := if result.succeeded then ExternalResult.fromWord (externalCallResultWord result)
        else Inhabited.default }

def tryExternalCallWords {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (adv : AdversaryModel := .stub) : Contract (Bool × α) := do
  let result ← commonExternalCall adv (linkedCallSite name args 1)
  pure (result.succeeded,
    if result.succeeded then ExternalResult.fromWord (externalCallResultWord result)
    else Inhabited.default)

def externalCallBind {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α)
    (adv : AdversaryModel := .stub) : Contract Unit := fun state =>
  let words := args.flatMap ExternalArg.toWords
  match (commonExternalCall adv (linkedCallSite name words names.length)).run state with
  | .success (.success returndata) post =>
      if names.length ≤ returndata.length then .success () post
      else .revert "external call returned insufficient data" state
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

/-- Linked bind with explicit target and ETH value. Debits `selfBalance`
    only on success; insufficient balance or a failing stub reverts the
    pre-call world (including the journal). Callee state lives in
    `Verity.MultiContract`, not in this single-world stub. -/
def externalCallBindTo {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α)
    (adv : AdversaryModel := .stub) : Contract Unit :=
  fun state =>
    if value ≤ state.selfBalance then
      let argWords := args.flatMap ExternalArg.toWords
      let debited := { state with selfBalance := state.selfBalance - value }
      match (commonExternalCall adv
          (linkedCallSite name argWords names.length .call target.toNat value.val)).run debited with
      | .success (.success returndata) post =>
          if names.length ≤ returndata.length then ContractResult.success () post
          else ContractResult.revert "external call returned insufficient data" state
      | .success (.failure _) _ | .success (.revert _) _ =>
          ContractResult.revert "external call failed" state
      | .revert message _ => ContractResult.revert message state
    else
      ContractResult.revert "insufficient balance" state

/-! ### Run laws for the executable linked-call family

Successful primitives append exactly one journal entry, so a duplicated,
omitted, reordered, or argument-altered call is observably different at
`ContractState.calls`. A failing `externalCallBind` reverts, and `Contract.run`
rolls its failure entry back with the rest of the call state. All laws are
definitional (`rfl`). -/

@[simp] theorem recordLinkedCall_run (entry : ExternalCall) (s : ContractState) :
    (recordLinkedCall entry).run s =
      ContractResult.success () { s with calls := s.calls ++ [entry] } := rfl

@[simp] theorem externalCallBind_adv_apply {α : Type} [ExternalArg α]
    (adv : AdversaryModel) (names : List String) (name : String)
    (args : List α) (s : ContractState) :
    externalCallBind names name args adv s =
      match (commonExternalCall adv
          (linkedCallSite name (args.flatMap ExternalArg.toWords) names.length)).run s with
      | .success (.success returndata) post =>
          if names.length ≤ returndata.length then ContractResult.success () post
          else ContractResult.revert "external call returned insufficient data" s
      | .success (.failure _) _ | .success (.revert _) _ =>
          ContractResult.revert "external call failed" s
      | .revert message _ => ContractResult.revert message s := rfl

theorem externalCallBindTo_adv_apply {α : Type} [ExternalArg α]
    (adv : AdversaryModel)
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) (s : ContractState) :
    externalCallBindTo target value names name args adv s =
      if value ≤ s.selfBalance then
        let debited := { s with selfBalance := s.selfBalance - value }
        match (commonExternalCall adv
            (linkedCallSite name (args.flatMap ExternalArg.toWords) names.length
              .call target.toNat value.val)).run debited with
        | .success (.success returndata) post =>
            if names.length ≤ returndata.length then ContractResult.success () post
            else ContractResult.revert "external call returned insufficient data" s
        | .success (.failure _) _ | .success (.revert _) _ =>
            ContractResult.revert "external call failed" s
        | .revert message _ => ContractResult.revert message s
      else ContractResult.revert "insufficient balance" s := rfl

@[simp] theorem callResultWords_adv_run {α : Type} [ExternalResult α] [Inhabited α]
    (adv : AdversaryModel) (name : String) (args : List Uint256) (s : ContractState) :
    (callResultWords (α := α) name args adv).run s =
      (do
        let result ← commonExternalCall adv (linkedCallSite name args 1)
        pure
          (show Call.Result α from
          { success := result.succeeded
            returndata := if result.succeeded then ExternalResult.fromWord (externalCallResultWord result)
              else Inhabited.default })).run s := rfl

@[simp] theorem tryExternalCallWords_adv_run {α : Type} [ExternalResult α] [Inhabited α]
    (adv : AdversaryModel) (name : String) (args : List Uint256) (s : ContractState) :
    (tryExternalCallWords (α := α) name args adv).run s =
      (do
        let result ← commonExternalCall adv (linkedCallSite name args 1)
        pure (result.succeeded,
          if result.succeeded then ExternalResult.fromWord (externalCallResultWord result)
          else Inhabited.default)).run s := rfl

/-! The PR1 `.stub` laws retain their original names and propositions. -/

@[simp] theorem externalCallBind_run {α : Type} [ExternalArg α]
    (names : List String) (name : String) (args : List α) (s : ContractState) :
    (externalCallBind names name args).run s =
      if externalCallStubSuccess name then
        ContractResult.success ()
          { s with calls := s.calls ++
              [linkedCallEntry name (args.flatMap ExternalArg.toWords) .success
                (names.map fun _ =>
                  (externalCallStubWord name (args.flatMap ExternalArg.toWords) : Nat))] }
      else ContractResult.revert "external call failed" s := by
  by_cases h : name = "fail" <;>
    simp [Contract.run, externalCallBind, commonExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
      Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
      Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
      Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
      Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
      externalCallStubSuccess, linkedCallSite, linkedCallEntry, externalCallStubWord, h]

theorem externalCallBindTo_run {α : Type} [ExternalArg α]
    (target : Address) (value : Uint256)
    (names : List String) (name : String) (args : List α) (s : ContractState) :
    (externalCallBindTo target value names name args).run s =
      if value ≤ s.selfBalance then
        if externalCallStubSuccess name then
          ContractResult.success ()
            { s with
              selfBalance := s.selfBalance - value
              calls := s.calls ++
                [linkedCallEntryTo name target value (args.flatMap ExternalArg.toWords)
                  .success
                  (names.map fun _ =>
                    (externalCallStubWord name (args.flatMap ExternalArg.toWords) : Nat))] }
        else ContractResult.revert "external call failed" s
      else ContractResult.revert "insufficient balance" s := by
  by_cases hbal : value ≤ s.selfBalance
  · by_cases h : name = "fail"
    · simp [Contract.run, externalCallBindTo, commonExternalCall,
        Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
        Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
        Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
        Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
        Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
        Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
        Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
        Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
        Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
        externalCallStubSuccess, linkedCallSite, linkedCallEntryTo, linkedCallEntry,
        externalCallStubWord, hbal, h]
    · simp [Contract.run, externalCallBindTo, commonExternalCall,
        Compiler.CompilationModel.DenoteExternalCalls.externalCall,
        Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
        Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
        Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
        Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
        Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
        Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
        Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
        Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
        Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
        externalCallStubSuccess, linkedCallSite, linkedCallEntryTo, linkedCallEntry,
        externalCallStubWord, hbal, h]
  · simp [Contract.run, externalCallBindTo, hbal]

@[simp] theorem callResultWords_run {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (s : ContractState) :
    (callResultWords (α := α) name args).run s =
      ContractResult.success
        { success := externalCallStubSuccess name
          returndata :=
            if externalCallStubSuccess name then
              ExternalResult.fromWord (externalCallStubWord name args)
            else Inhabited.default }
        { s with calls := s.calls ++
            [linkedCallEntry name args
              (if externalCallStubSuccess name then .success else .failure)
              (if externalCallStubSuccess name then
                [(externalCallStubWord name args : Nat)]
              else [])] } := by
  by_cases h : name = "fail" <;>
    simp [callResultWords, commonExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
      Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
      Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
      Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.succeeded,
      Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
      Contract.run, Verity.bind, Verity.pure, Verity.instMonadContract, Bind.bind, Pure.pure,
      linkedCallSite, linkedCallEntry,
      externalCallStubSuccess, externalCallStubWord, externalCallResultWord, h]

@[simp] theorem tryExternalCallWords_run {α : Type} [ExternalResult α] [Inhabited α]
    (name : String) (args : List Uint256) (s : ContractState) :
    (tryExternalCallWords (α := α) name args).run s =
      ContractResult.success
        (externalCallStubSuccess name,
          if externalCallStubSuccess name then
            ExternalResult.fromWord (externalCallStubWord name args)
          else Inhabited.default)
        { s with calls := s.calls ++
            [linkedCallEntry name args
              (if externalCallStubSuccess name then .success else .failure)
              (if externalCallStubSuccess name then
                [(externalCallStubWord name args : Nat)]
              else [])] } := by
  by_cases h : name = "fail" <;>
    simp [tryExternalCallWords, commonExternalCall,
      Compiler.CompilationModel.DenoteExternalCalls.externalCall,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
      Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
      Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
      Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
      Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
      Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.succeeded,
      Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
      Contract.run, Verity.bind, Verity.pure, Verity.instMonadContract, Bind.bind, Pure.pure,
      linkedCallSite, linkedCallEntry,
      externalCallStubSuccess, externalCallStubWord, externalCallResultWord, h]

private def erc20ReadStubWord (name : String) (args : List Uint256) : Uint256 :=
  externalCallStubWord name args

@[simp] theorem erc20ReadStubWord_eq (name : String) (args : List Uint256) :
    erc20ReadStubWord name args = externalCallStubWord name args := rfl
macro_rules
  | `(term| externalCall $name:ident [ $[$args:term],* ]) =>
      `(externalCallWords $(Lean.quote (toString name.getId))
          (List.flatten [ $[ExternalArg.toWords $args],* ]))
  | `(term| externalCall $name:str [ $[$args:term],* ]) =>
      `(externalCallWords $name (List.flatten [ $[ExternalArg.toWords $args],* ]))
  | `(term| callResult $name:str [ $[$args:term],* ]) =>
      `(callResultWords $name (List.flatten [ $[ExternalArg.toWords $args],* ]))
  | `(term| callResult $name:ident [ $[$args:term],* ]) =>
      `(callResultWords $(Lean.quote (toString name.getId))
          (List.flatten [ $[ExternalArg.toWords $args],* ]))
  | `(term| tryExternalCall $name:str [ $[$args:term],* ]) =>
      `(tryExternalCallWords $name (List.flatten [ $[ExternalArg.toWords $args],* ]))
  | `(term| tryExternalCall $name:ident [ $[$args:term],* ]) =>
      `(tryExternalCallWords $(Lean.quote (toString name.getId))
          (List.flatten [ $[ExternalArg.toWords $args],* ]))
def getMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset : Uint256) :
    Contract Uint256 := pure 0
def setMappingWord (_slot : StorageSlot (Uint256 → Uint256)) (_key _wordOffset _value : Uint256) :
    Contract Unit := pure ()
def getMappingN {κ α : Type} (_slot : StorageSlot α) (_keys : List κ) :
    Contract Uint256 := pure 0
def setMappingN {κ α : Type} (_slot : StorageSlot α) (_keys : List κ) (_value : Uint256) :
    Contract Unit := pure ()

def structMember {κ α : Type} [Inhabited α] (_field : String) (_key : κ) (_member : String) :
    Contract α := pure (Inhabited.default : α)
def structMember2 {κ₁ κ₂ α : Type} [Inhabited α]
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) : Contract α :=
  pure (Inhabited.default : α)
def structMembers {κ α : Type} [Inhabited α]
    (_field : String) (_key : κ) (_members : List String) : α := (Inhabited.default : α)
def structMembers2 {κ₁ κ₂ α : Type} [Inhabited α]
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_members : List String) : α :=
  (Inhabited.default : α)
def setStructMember {κ α : Type} (_field : String) (_key : κ) (_member : String) (_value : α) :
    Contract Unit := pure ()
def setStructMember2 {κ₁ κ₂ α : Type}
    (_field : String) (_key1 : κ₁) (_key2 : κ₂) (_member : String) (_value : α) : Contract Unit := pure ()
def erc20WriteEntry (name : String) (token : Address) (args : List Uint256) : ExternalCall :=
  { linkedCallEntry name args with target := token.toNat }

def erc20ReadEntry (name : String) (token : Address) (args : List Uint256)
    (result : Uint256) : ExternalCall :=
  { linkedCallEntry name args .success [(result : Nat)] with
      kind := .staticcall
      target := token.toNat }

def erc20Read (adv : AdversaryModel) (name : String) (token : Address)
    (args : List Uint256) : Contract Uint256 := fun state =>
  match (commonExternalCall adv
      (linkedCallSite name args 1 .staticcall token.toNat 0
        [Verity.addressToWord token])).run state with
  | .success (.success [word]) post =>
      .success (Core.Uint256.ofNat word) post
  | .success (.success _) _ =>
      .revert "external call returned invalid data" state
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

def erc20Write (adv : AdversaryModel) (name : String) (token : Address)
    (args : List Uint256) : Contract Unit := fun state =>
  match (commonExternalCall adv
      (linkedCallSite name args 0 .call token.toNat)).run state with
  | .success (.success _) post => .success () post
  | .success (.failure _) _ | .success (.revert _) _ =>
      .revert "external call failed" state
  | .revert message _ => .revert message state

def safeTransfer (token toAddr : Address) (amount : Uint256) (adv : AdversaryModel := .stub) : Contract Unit :=
  erc20Write adv "safeTransfer" token [Verity.addressToWord toAddr, amount]
def safeTransferFrom (token fromAddr toAddr : Address) (amount : Uint256)
    (adv : AdversaryModel := .stub) : Contract Unit :=
  erc20Write adv "safeTransferFrom" token
    [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]
def safeApprove (token spender : Address) (amount : Uint256) (adv : AdversaryModel := .stub) : Contract Unit :=
  erc20Write adv "safeApprove" token [Verity.addressToWord spender, amount]
def legacyStringSafeTransfer (token toAddr : Address) (amount : Uint256)
    (adv : AdversaryModel := .stub) : Contract Unit :=
  erc20Write adv "legacyStringSafeTransfer" token [Verity.addressToWord toAddr, amount]
def legacyStringSafeTransferFrom (token fromAddr toAddr : Address) (amount : Uint256)
    (adv : AdversaryModel := .stub) : Contract Unit :=
  erc20Write adv "legacyStringSafeTransferFrom" token
    [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]

@[simp] theorem safeTransfer_adv_run (adv : AdversaryModel) (token toAddr : Address)
    (amount : Uint256) (s : ContractState) :
    (safeTransfer token toAddr amount adv).run s =
      (erc20Write adv "safeTransfer" token [Verity.addressToWord toAddr, amount]).run s := rfl

@[simp] theorem safeTransferFrom_adv_run (adv : AdversaryModel) (token fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) :
    (safeTransferFrom token fromAddr toAddr amount adv).run s =
      (erc20Write adv "safeTransferFrom" token
        [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]).run s := rfl

@[simp] theorem safeApprove_adv_run (adv : AdversaryModel) (token spender : Address) (amount : Uint256)
    (s : ContractState) :
    (safeApprove token spender amount adv).run s =
      (erc20Write adv "safeApprove" token [Verity.addressToWord spender, amount]).run s := rfl

theorem erc20Write_stub_run (name : String) (token : Address)
    (args : List Uint256) (s : ContractState) (h : name ≠ "fail") :
    (erc20Write .stub name token args).run s =
      ContractResult.success ()
        { s with calls := s.calls ++ [erc20WriteEntry name token args] } := by
  simp [erc20Write, commonExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
    Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
    Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
    Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
    Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
    Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
    Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
    Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
    Contract.run, linkedCallSite, erc20WriteEntry, linkedCallEntry, h]

@[simp] theorem safeTransfer_run (token toAddr : Address) (amount : Uint256)
    (s : ContractState) :
    (safeTransfer token toAddr amount).run s =
      ContractResult.success ()
        { s with calls := s.calls ++
            [erc20WriteEntry "safeTransfer" token
              [Verity.addressToWord toAddr, amount]] } := by
  simpa [safeTransfer] using
    erc20Write_stub_run "safeTransfer" token [Verity.addressToWord toAddr, amount] s (by decide)

@[simp] theorem safeTransferFrom_run (token fromAddr toAddr : Address) (amount : Uint256)
    (s : ContractState) :
    (safeTransferFrom token fromAddr toAddr amount).run s =
      ContractResult.success ()
        { s with calls := s.calls ++
            [erc20WriteEntry "safeTransferFrom" token
              [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount]] } := by
  simpa [safeTransferFrom] using erc20Write_stub_run "safeTransferFrom" token
    [Verity.addressToWord fromAddr, Verity.addressToWord toAddr, amount] s (by decide)

@[simp] theorem safeApprove_run (token spender : Address) (amount : Uint256)
    (s : ContractState) :
    (safeApprove token spender amount).run s =
      ContractResult.success ()
        { s with calls := s.calls ++
            [erc20WriteEntry "safeApprove" token
              [Verity.addressToWord spender, amount]] } := by
  simpa [safeApprove] using
    erc20Write_stub_run "safeApprove" token [Verity.addressToWord spender, amount] s (by decide)

def balanceOf (token owner : Address) (adv : AdversaryModel := .stub) : Contract Uint256 :=
  erc20Read adv "balanceOf" token [Verity.addressToWord owner]
def allowance (token owner spender : Address) (adv : AdversaryModel := .stub) : Contract Uint256 :=
  erc20Read adv "allowance" token
    [Verity.addressToWord owner, Verity.addressToWord spender]
def totalSupply (token : Address) (adv : AdversaryModel := .stub) : Contract Uint256 :=
  erc20Read adv "totalSupply" token []

@[simp] theorem balanceOf_adv_run (adv : AdversaryModel) (token owner : Address) (s : ContractState) :
    (balanceOf token owner adv).run s =
      (erc20Read adv "balanceOf" token [Verity.addressToWord owner]).run s := rfl

@[simp] theorem allowance_adv_run (adv : AdversaryModel) (token owner spender : Address)
    (s : ContractState) :
    (allowance token owner spender adv).run s =
      (erc20Read adv "allowance" token
        [Verity.addressToWord owner, Verity.addressToWord spender]).run s := rfl

@[simp] theorem totalSupply_adv_run (adv : AdversaryModel) (token : Address) (s : ContractState) :
    (totalSupply token adv).run s = (erc20Read adv "totalSupply" token []).run s := rfl

theorem erc20Read_stub_run (name : String) (token : Address)
    (args : List Uint256) (s : ContractState) (h : name ≠ "fail") :
    (erc20Read .stub name token args).run s =
      let result := erc20ReadStubWord name (Verity.addressToWord token :: args)
      ContractResult.success result
        { s with calls := s.calls ++ [erc20ReadEntry name token args result] } := by
  simp [erc20Read, commonExternalCall,
    Compiler.CompilationModel.DenoteExternalCalls.externalCall,
    Compiler.CompilationModel.DenoteExternalCalls.denoteCallJournaled,
    Compiler.CompilationModel.DenoteExternalCalls.denoteCall,
    Compiler.CompilationModel.DenoteExternalCalls.chargedGas,
    Compiler.CompilationModel.DenoteExternalCalls.journalEntry,
    Compiler.CompilationModel.DenoteExternalCalls.CallKind.toJournal,
    Compiler.CompilationModel.DenoteExternalCalls.CallControl.toJournal,
    Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.control,
    Compiler.CompilationModel.DenoteExternalCalls.ExternalCallResult.returndata,
    Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel.stub,
    Contract.run, Verity.bind, Verity.pure, Verity.instMonadContract, Bind.bind, Pure.pure,
    linkedCallSite, externalCallResultWord, erc20ReadStubWord, externalCallStubWord,
    erc20ReadEntry, linkedCallEntry, h]

@[simp] theorem balanceOf_run (token owner : Address) (s : ContractState) :
    (balanceOf token owner).run s =
      let result := erc20ReadStubWord "balanceOf"
        [Verity.addressToWord token, Verity.addressToWord owner]
      ContractResult.success result
        { s with calls := s.calls ++
            [erc20ReadEntry "balanceOf" token [Verity.addressToWord owner] result] } := by
  simpa [balanceOf] using erc20Read_stub_run "balanceOf" token
    [Verity.addressToWord owner] s (by decide)

@[simp] theorem allowance_run (token owner spender : Address) (s : ContractState) :
    (allowance token owner spender).run s =
      let result := erc20ReadStubWord "allowance"
        [Verity.addressToWord token, Verity.addressToWord owner,
          Verity.addressToWord spender]
      ContractResult.success result
        { s with calls := s.calls ++
            [erc20ReadEntry "allowance" token
              [Verity.addressToWord owner, Verity.addressToWord spender] result] } := by
  simpa [allowance] using erc20Read_stub_run "allowance" token
    [Verity.addressToWord owner, Verity.addressToWord spender] s (by decide)

@[simp] theorem totalSupply_run (token : Address) (s : ContractState) :
    (totalSupply token).run s =
      let result := erc20ReadStubWord "totalSupply" [Verity.addressToWord token]
      ContractResult.success result
        { s with calls := s.calls ++ [erc20ReadEntry "totalSupply" token [] result] } := by
  simpa [totalSupply] using erc20Read_stub_run "totalSupply" token [] s (by decide)
def forEach (_name : String) (_count : Uint256) (body : Contract Unit) : Contract Unit := body
def blockTimestamp : Contract Uint256 := Verity.blockTimestamp
def blockNumber : Contract Uint256 := Verity.blockNumber
def blobbasefee : Contract Uint256 := Verity.blobbasefee
def contractAddress : Contract Address := Verity.contractAddress
def chainid : Contract Uint256 := Verity.chainid

class StorageKey (α : Type) where
  toWord : α → Nat

instance : StorageKey Uint256 where
  toWord key := key.val

instance : StorageKey Address where
  toWord key := key.toNat

class StorageWord (α : Type) where
  fromWord : Uint256 → α
  toWord : α → Uint256

instance : StorageWord Uint256 where
  fromWord word := word
  toWord word := word

instance : StorageWord Uint16 where
  fromWord word := Verity.wordToUint16 word
  toWord value := value.toUint256

instance : StorageWord Bool where
  fromWord word := word != 0
  toWord value := Verity.boolToWord value

instance : StorageWord Address where
  fromWord word := Verity.wordToAddress word
  toWord addr := Verity.addressToWord addr

def structSlot (baseSlot : Nat) (key : Nat) (wordOffset : Nat) : Nat :=
  (Compiler.Proofs.abstractMappingSlot baseSlot key + wordOffset) % Compiler.Constants.evmModulus

def structSlot2 (baseSlot : Nat) (key1 key2 : Nat) (wordOffset : Nat) : Nat :=
  (Compiler.Proofs.abstractMappingSlot (Compiler.Proofs.abstractMappingSlot baseSlot key1) key2 + wordOffset) %
    Compiler.Constants.evmModulus

private def packedMask (width : Nat) : Nat :=
  2 ^ width - 1

private def decodePackedWord (word : Uint256) (offset width : Nat) : Uint256 :=
  Verity.Core.Uint256.and (Verity.Core.Uint256.shr offset word) (packedMask width)

private def encodePackedWord (current value : Uint256) (offset width : Nat) : Uint256 :=
  let mask := packedMask width
  let shiftedMask := Verity.Core.Uint256.shl offset mask
  let packedValue := Verity.Core.Uint256.and value mask
  let cleared := Verity.Core.Uint256.and current (Verity.Core.Uint256.not shiftedMask)
  Verity.Core.Uint256.or cleared (Verity.Core.Uint256.shl offset packedValue)

def structMemberAt {κ α : Type} [StorageKey κ] [StorageWord α]
    (baseSlot : Nat) (wordOffset : Nat) (packed : Option (Nat × Nat)) (key : κ) :
    Contract α :=
  fun state =>
    let targetSlot := structSlot baseSlot (StorageKey.toWord key) wordOffset
    let raw := state.storage targetSlot
    let word := match packed with
      | none => raw
      | some (offset, width) => decodePackedWord raw offset width
    ContractResult.success (StorageWord.fromWord word) state

def structMember2At {κ₁ κ₂ α : Type} [StorageKey κ₁] [StorageKey κ₂] [StorageWord α]
    (baseSlot : Nat) (wordOffset : Nat) (packed : Option (Nat × Nat)) (key1 : κ₁) (key2 : κ₂) :
    Contract α :=
  fun state =>
    let targetSlot := structSlot2 baseSlot (StorageKey.toWord key1) (StorageKey.toWord key2) wordOffset
    let raw := state.storage targetSlot
    let word := match packed with
      | none => raw
      | some (offset, width) => decodePackedWord raw offset width
    ContractResult.success (StorageWord.fromWord word) state

def setStructMemberAt {κ α : Type} [StorageKey κ] [StorageWord α]
    (baseSlot : Nat) (wordOffset : Nat) (packed : Option (Nat × Nat)) (key : κ) (value : α) :
    Contract Unit :=
  fun state =>
    let targetSlot := structSlot baseSlot (StorageKey.toWord key) wordOffset
    let word := StorageWord.toWord value
    let stored :=
      match packed with
      | none => word
      | some (offset, width) => encodePackedWord (state.storage targetSlot) word offset width
    ContractResult.success () (state.writeSlot targetSlot stored)

def setStructMember2At {κ₁ κ₂ α : Type} [StorageKey κ₁] [StorageKey κ₂] [StorageWord α]
    (baseSlot : Nat) (wordOffset : Nat) (packed : Option (Nat × Nat)) (key1 : κ₁) (key2 : κ₂)
    (value : α) : Contract Unit :=
  fun state =>
    let targetSlot := structSlot2 baseSlot (StorageKey.toWord key1) (StorageKey.toWord key2) wordOffset
    let word := StorageWord.toWord value
    let stored :=
      match packed with
      | none => word
      | some (offset, width) => encodePackedWord (state.storage targetSlot) word offset width
    ContractResult.success () (state.writeSlot targetSlot stored)


end Contracts
