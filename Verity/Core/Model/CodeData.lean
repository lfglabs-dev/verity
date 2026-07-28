import Compiler.Keccak.Sponge
import Verity.Core.Address
import Verity.Core.Uint256

/-!
# Code-as-data byte layouts

This module gives the model layer a typed surface for SSTORE2-style runtime
code that stores an opaque byte payload after a fixed prefix, plus the CREATE2
preimage shape used to address contracts deployed from such initcode.

The payload remains an uninterpreted `ByteArray`; typed ABI decoding is left to
the dynamic ABI codec work.
-/

namespace Verity.Core.Model

namespace CodeData

/-- Model-level byte concatenation with transparent length behavior. -/
def byteAppend (lhs rhs : ByteArray) : ByteArray :=
  ⟨lhs.data ++ rhs.data⟩

infixl:65 " +++ " => byteAppend

@[simp] theorem byteAppend_size (lhs rhs : ByteArray) :
    (lhs +++ rhs).size = lhs.size + rhs.size := by
  simp only [byteAppend, ByteArray.size, Array.size_append]

/-- A byte layout whose runtime code is exactly `codePrefix ++ payload`. -/
structure Layout where
  codePrefix : ByteArray
  payload : ByteArray

/-- The SSTORE2 runtime prefix: `STOP`, followed by opaque payload bytes. -/
def sstore2Prefix : ByteArray := ⟨#[0x00]⟩

/-- Build an SSTORE2-style layout from opaque payload bytes. -/
def sstore2 (payload : ByteArray) : Layout :=
  { codePrefix := sstore2Prefix, payload }

/-- Runtime code materialized by a code-data layout. -/
def Layout.runtimeCode (layout : Layout) : ByteArray :=
  layout.codePrefix +++ layout.payload

/-- Byte offset at which the payload begins in the runtime code. -/
def Layout.payloadOffset (layout : Layout) : Nat :=
  layout.codePrefix.size

/-- Payload length in bytes. -/
def Layout.payloadLength (layout : Layout) : Nat :=
  layout.payload.size

@[simp] theorem runtimeCode_eq_prefix_append_payload (layout : Layout) :
    layout.runtimeCode = layout.codePrefix +++ layout.payload := rfl

@[simp] theorem payloadOffset_eq_prefix_size (layout : Layout) :
    layout.payloadOffset = layout.codePrefix.size := rfl

@[simp] theorem payloadLength_eq_payload_size (layout : Layout) :
    layout.payloadLength = layout.payload.size := rfl

@[simp] theorem runtimeCode_size (layout : Layout) :
    layout.runtimeCode.size = layout.codePrefix.size + layout.payload.size := by
  simp [Layout.runtimeCode]

@[simp] theorem runtimeCode_size_eq_offset_add_payloadLength (layout : Layout) :
    layout.runtimeCode.size = layout.payloadOffset + layout.payloadLength := by
  simp [Layout.payloadOffset, Layout.payloadLength]

@[simp] theorem sstore2_prefix_size : sstore2Prefix.size = 1 := rfl

@[simp] theorem sstore2_payloadOffset (payload : ByteArray) :
    (sstore2 payload).payloadOffset = 1 := rfl

@[simp] theorem sstore2_runtimeCode (payload : ByteArray) :
    (sstore2 payload).runtimeCode = sstore2Prefix +++ payload := rfl

/--
Model-level initcode certificate: `code` is the creation-code byte string and
`runtimeCode` is the byte string produced by executing it.
-/
structure InitCode where
  code : ByteArray
  runtimeCode : ByteArray

/-- Observable runtime code produced by an initcode certificate. -/
def InitCode.deployRuntime (init : InitCode) : ByteArray :=
  init.runtimeCode

/--
Generic verified initcode builder. The concrete creation-code bytes are kept
explicit, while the deployed runtime is pinned to the requested runtime bytes.
-/
def buildInitCode (code runtimeCode : ByteArray) : InitCode :=
  { code, runtimeCode }

/-- Build initcode whose deployed runtime is a code-data layout. -/
def buildLayoutInitCode (code : ByteArray) (layout : Layout) : InitCode :=
  buildInitCode code layout.runtimeCode

@[simp] theorem buildInitCode_deployRuntime (code runtimeCode : ByteArray) :
    (buildInitCode code runtimeCode).deployRuntime = runtimeCode := rfl

@[simp] theorem buildLayoutInitCode_deployRuntime (code : ByteArray) (layout : Layout) :
    (buildLayoutInitCode code layout).deployRuntime = layout.codePrefix +++ layout.payload := rfl

end CodeData

namespace Create2

/-- Big-endian byte representation of `n`, padded/truncated to `width` bytes. -/
def natBytesBE (width n : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin width =>
    UInt8.ofNat ((n / (256 ^ (width - 1 - i.val))) % 256)⟩

/-- Big-endian 20-byte representation of an EVM address. -/
def addressBytes (deployer : Address) : ByteArray :=
  natBytesBE 20 deployer.toNat

/-- Big-endian 32-byte representation of an EVM word. -/
def wordBytes (word : Uint256) : ByteArray :=
  natBytesBE 32 word.val

/-- The fixed CREATE2 preimage marker byte, `0xff`. -/
def marker : ByteArray := ⟨#[0xff]⟩

/-- Typed CREATE2 preimage fields. -/
structure Preimage where
  deployer : Address
  salt : Uint256
  initcodeHash : Uint256

/-- Byte encoding of the EIP-1014 CREATE2 preimage. -/
def Preimage.bytes (preimage : Preimage) : ByteArray :=
  CodeData.byteAppend
    (CodeData.byteAppend
      (CodeData.byteAppend marker (addressBytes preimage.deployer))
      (wordBytes preimage.salt))
    (wordBytes preimage.initcodeHash)

/-- Keccak-256 digest of a typed CREATE2 preimage. -/
def Preimage.hash (preimage : Preimage) : ByteArray :=
  KeccakEngine.keccak256 preimage.bytes

/-- CREATE2 address derived from the low 160 bits of the preimage hash. -/
def Preimage.address (preimage : Preimage) : Address :=
  Address.ofNat (KeccakEngine.byteArrayToNatBE preimage.hash)

/-- Model-level CREATE2 address derivation from typed fields. -/
def create2Address (salt initcodeHash : Uint256) (deployer : Address) : Address :=
  ({ deployer, salt, initcodeHash } : Preimage).address

@[simp] theorem natBytesBE_size (width n : Nat) :
    (natBytesBE width n).size = width := by
  simp [natBytesBE, ByteArray.size]

@[simp] theorem addressBytes_size (deployer : Address) :
    (addressBytes deployer).size = 20 := by
  simp [addressBytes]

@[simp] theorem wordBytes_size (word : Uint256) :
    (wordBytes word).size = 32 := by
  simp [wordBytes]

@[simp] theorem marker_size : marker.size = 1 := rfl

@[simp] theorem preimage_bytes_eq (preimage : Preimage) :
    preimage.bytes =
      CodeData.byteAppend
        (CodeData.byteAppend
          (CodeData.byteAppend marker (addressBytes preimage.deployer))
          (wordBytes preimage.salt))
        (wordBytes preimage.initcodeHash) := rfl

@[simp] theorem preimage_bytes_size (preimage : Preimage) :
    preimage.bytes.size = 85 := by
  simp [Preimage.bytes]

@[simp] theorem preimage_hash_eq_keccak (preimage : Preimage) :
    preimage.hash = KeccakEngine.keccak256 preimage.bytes := rfl

@[simp] theorem create2Address_eq_preimage_address
    (salt initcodeHash : Uint256) (deployer : Address) :
    create2Address salt initcodeHash deployer =
      ({ deployer, salt, initcodeHash } : Preimage).address := rfl

end Create2

end Verity.Core.Model
