import Verity.Core.Model.Types

/-!
# Typed CodeData ABI payloads

This module layers a `ParamType`-indexed surface on top of the lower-level
SSTORE2 byte layout in `Verity.Core.Model.CodeData`.

The environment-free `read` name is provided for API discovery, but an EVM
address alone is not enough information to recover deployed runtime code. The
executable/readable model API is therefore `readFrom`, which takes an explicit
snapshot of code-data values at addresses.
-/

namespace Verity.Core.Model

namespace CodeData

open Compiler.CompilationModel

/-- Untyped runtime values used by the model-level ABI encoder. -/
inductive RawValue where
  | word (value : Nat)
  | bytes (value : ByteArray)
  | array (values : List RawValue)
  | tuple (values : List RawValue)

/-- Public `ParamType`-indexed value family for CodeData payloads. -/
abbrev Value (_p : ParamType) := RawValue

private def zeroBytes (n : Nat) : ByteArray :=
  ⟨Array.replicate n 0⟩

private def pad32 (n : Nat) : Nat :=
  (32 - (n % 32)) % 32

private def padRight32 (bytes : ByteArray) : ByteArray :=
  bytes +++ zeroBytes (pad32 bytes.size)

private def wordBytesNat (n : Nat) : ByteArray :=
  Create2.natBytesBE 32 n

private def bytesValue : RawValue → ByteArray
  | .bytes bytes => bytes
  | _ => ByteArray.empty

private def wordValue : RawValue → Nat
  | .word value => value
  | _ => 0

private def listValue : RawValue → List RawValue
  | .array values => values
  | .tuple values => values
  | _ => []

mutual
  /-- Whether a parameter type contributes a runtime ABI tail. -/
  partial def isRuntimeDynamic : ParamType → Bool
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32 => false
    | .bytes | .string | .array _ => true
    | .fixedArray elemTy _ => isRuntimeDynamic elemTy
    | .tuple elemTys => isRuntimeDynamicList elemTys
    | .adt _ _ => false
    | .newtypeOf _ baseType => isRuntimeDynamic baseType

  partial def isRuntimeDynamicList : List ParamType → Bool
    | [] => false
    | ty :: rest => isRuntimeDynamic ty || isRuntimeDynamicList rest
end

mutual
  /-- ABI head bytes contributed to a parent value. Dynamic children occupy one offset word. -/
  partial def parentHeadBytes : ParamType → Nat
    | .bytes | .string | .array _ => 32
    | .tuple elemTys =>
        if isRuntimeDynamicList elemTys then 32 else localHeadBytes (.tuple elemTys)
    | .fixedArray elemTy n =>
        if isRuntimeDynamic (.fixedArray elemTy n) then 32 else n * parentHeadBytes elemTy
    | .newtypeOf _ baseType => parentHeadBytes baseType
    | .adt _ maxFields => 32 * (1 + maxFields)
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32 => 32

  /-- ABI head bytes within the local encoding of a value. -/
  partial def localHeadBytes : ParamType → Nat
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32
    | .bytes | .string | .array _ => 32
    | .fixedArray elemTy n => n * parentHeadBytes elemTy
    | .tuple elemTys => elemTys.foldl (fun acc ty => acc + parentHeadBytes ty) 0
    | .adt _ maxFields => 32 * (1 + maxFields)
    | .newtypeOf _ baseType => localHeadBytes baseType
end

private def encodeScalar (ty : ParamType) (v : RawValue) : ByteArray :=
  match ty with
  | .uint8 => wordBytesNat (wordValue v % 256)
  | .uint16 => wordBytesNat (wordValue v % 65536)
  | .address => wordBytesNat (wordValue v % Address.modulus)
  | .bool => wordBytesNat (if wordValue v = 0 then 0 else 1)
  | .uint256 | .int256 | .bytes32 => wordBytesNat (wordValue v)
  | .adt _ _ | .bytes | .string | .array _ | .fixedArray _ _ | .tuple _ | .newtypeOf _ _ =>
      wordBytesNat 0

private def takeOrDefault (xs : List RawValue) (idx : Nat) : RawValue :=
  xs[idx]?.getD (.word 0)

mutual
  /-- Local ABI encoding of a value after any parent offset has been resolved. -/
  partial def encodeBody (ty : ParamType) (v : Value ty) : ByteArray :=
    match ty with
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32 =>
        encodeScalar ty v
    | .bytes | .string =>
        let bytes := bytesValue v
        wordBytesNat bytes.size +++ padRight32 bytes
    | .array elemTy =>
        encodeArray elemTy (listValue v)
    | .fixedArray elemTy n =>
        encodeFixedArray elemTy n (listValue v)
    | .tuple elemTys =>
        encodeTuple elemTys (listValue v)
    | .adt _ maxFields =>
        let fields := listValue v
        (List.range (1 + maxFields)).foldl
          (fun acc i => acc +++ wordBytesNat (wordValue (takeOrDefault fields i)))
          ByteArray.empty
    | .newtypeOf _ baseType =>
        encodeBody baseType v

  partial def encodeTuple (tys : List ParamType) (values : List RawValue) : ByteArray :=
    let headSize := tys.foldl (fun acc ty => acc + parentHeadBytes ty) 0
    let (_, head, tail) := tys.foldl
      (fun (state : Nat × ByteArray × ByteArray) ty =>
        let (idx, head, tail) := state
        let value := takeOrDefault values idx
        if isRuntimeDynamic ty then
          let body := encodeBody ty value
          (idx + 1, head +++ wordBytesNat (headSize + tail.size), tail +++ body)
        else
          (idx + 1, head +++ encodeBody ty value, tail))
      (0, ByteArray.empty, ByteArray.empty)
    head +++ tail

  partial def encodeArray (elemTy : ParamType) (values : List RawValue) : ByteArray :=
    wordBytesNat values.length +++ encodeFixedArray elemTy values.length values

  partial def encodeFixedArray (elemTy : ParamType) (n : Nat) (values : List RawValue) : ByteArray :=
    let elems := List.range n
    if isRuntimeDynamic elemTy then
      let headSize := n * 32
      let (_, head, tail) := elems.foldl
        (fun (state : Nat × ByteArray × ByteArray) i =>
          let (_idx, head, tail) := state
          let body := encodeBody elemTy (takeOrDefault values i)
          (i + 1, head +++ wordBytesNat (headSize + tail.size), tail +++ body))
        (0, ByteArray.empty, ByteArray.empty)
      head +++ tail
    else
      elems.foldl
        (fun acc i => acc +++ encodeBody elemTy (takeOrDefault values i))
        ByteArray.empty
end

/-- ABI encoding of a single `ParamType` value as `abi.encode(value)`. -/
def abiEncode (p : ParamType) (v : Value p) : ByteArray :=
  if isRuntimeDynamic p then
    wordBytesNat 32 +++ encodeBody p v
  else
    encodeBody p v

/-- SSTORE2 payload bytes: the runtime-sized ABI encoding. -/
def store (p : ParamType) (v : Value p) : ByteArray :=
  abiEncode p v

/-- SSTORE2 runtime code for returning the stored ABI payload. -/
def returnData (p : ParamType) (v : Value p) : ByteArray :=
  sstore2Prefix +++ store p v

/-- Deterministic model id for a CodeData payload.

The production CREATE2 address still requires deployer and salt. This model id
hashes the observable SSTORE2 runtime bytes and truncates through `Address`.
-/
def id (p : ParamType) (v : Value p) : Address :=
  Address.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 (returnData p v)))

/-- Runtime-sized ABI payload length for a concrete value. -/
def runtimeSizedLayout (p : ParamType) (v : Value p) : Nat :=
  (store p v).size

/-- Snapshot of deployed CodeData values indexed by address. -/
abbrev Store := Address → Option RawValue

/-- Snapshot containing exactly one freshly stored CodeData value. -/
def singletonStore (p : ParamType) (v : Value p) : Store :=
  fun addr => if addr = id p v then some v else none

/-- Read from an explicit CodeData snapshot. -/
def readFrom (store : Store) (addr : Address) (_p : ParamType) : Except String RawValue :=
  match store addr with
  | some value => Except.ok value
  | none => Except.error "CodeData.read requires a code snapshot for extcodecopy"

/-- Environment-free read placeholder. Use `readFrom` for executable semantics. -/
def read (addr : Address) (p : ParamType) : Except String (Value p) :=
  readFrom (fun _ => none) addr p

@[simp] theorem codeData_returnData_size (p : ParamType) (v : Value p) :
    (returnData p v).size = 1 + (store p v).size := by
  simp [returnData]

theorem codeData_size_correct (p : ParamType) (v : Value p) :
    runtimeSizedLayout p v = (store p v).size := rfl

theorem codeData_read_store (p : ParamType) (v : Value p) :
    readFrom (singletonStore p v) (id p v) p = Except.ok v := by
  simp [readFrom, singletonStore]

theorem codeData_roundtrip
    {snapshot : Store} {addr : Address} {p : ParamType} {v : Value p}
    (hread : readFrom snapshot addr p = Except.ok v) :
    (readFrom snapshot addr p >>= fun value => Except.ok (store p value)) =
      Except.ok (store p v) := by
  rw [hread]
  rfl

end CodeData

end Verity.Core.Model
