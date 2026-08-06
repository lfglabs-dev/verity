import Verity.Core.Model.DenoteExternalCalls
import Verity.Core.Model.DynamicAbi

/-!
# Dynamic memory, bytes, and ABI denotation

This module is the byte-precise memory layer of the canonical denotation.  It
models the operations emitted by Verity's Yul lowering: `mstore`, `mload`,
`mstore8`, `calldatacopy`, `returndatacopy`, `mcopy`, `returndatasize`,
`return`, and `revert`.  Memory is zero-filled and expands in 32-byte words through the
highest byte touched, exactly as EVM memory does.  `returndatacopy` is the only
operation in this slice that can fail: unlike calldata, returndata is not
zero-extended.

`codecopy` and `extcodecopy` are out of scope.  Gas accounting and the EVM's
address-space limit are also deliberately outside the canonical functional
model.

`Denote` historically stores a whole word at each byte offset.  The final
section gives the exact composition boundary for that existing source model;
clients needing byte-level overlap use `Memory` below.
-/

namespace Compiler.CompilationModel.DenoteMemory

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.DenoteExternalCalls

abbrev Byte := Fin 256
abbrev Word := Fin 32 → Byte

def zeroByte : Byte := ⟨0, by decide⟩

/-- Runtime EVM memory. `size` is the expanded byte length and is always
intended to be a multiple of 32; `bytes` is total to expose zero-filled reads
without partial indexing. -/
structure Memory where
  bytes : Nat → Byte
  size : Nat

/-- A typed, bounded view of a contiguous memory range.  The dependent
`contents` field makes it impossible to observe a byte outside the declared
region without first supplying an in-bounds index. -/
structure MemoryRegion where
  offset : Nat
  size : Nat
  contents : Fin size → Byte

def Memory.empty : Memory :=
  { bytes := fun _ => zeroByte, size := 0 }

def expandedLength (endOffset : Nat) : Nat :=
  if endOffset = 0 then 0 else 32 * ((endOffset + 31) / 32)

def Memory.expand (memory : Memory) (endOffset : Nat) : Memory :=
  { memory with size := Nat.max memory.size (expandedLength endOffset) }

def Memory.readByte (memory : Memory) (offset : Nat) : Byte :=
  if offset < memory.size then memory.bytes offset else zeroByte

def Memory.writeByte (memory : Memory) (offset : Nat) (value : Byte) : Memory :=
  let expanded := memory.expand (offset + 1)
  { expanded with bytes := fun address => if address = offset then value else memory.readByte address }

def Memory.readWord (memory : Memory) (offset : Nat) : Word :=
  fun index => memory.readByte (offset + index)

def Memory.region (memory : Memory) (offset size : Nat) : MemoryRegion :=
  { offset := offset
    size := size
    contents := fun index => memory.readByte (offset + index) }

def Memory.writeWord (memory : Memory) (offset : Nat) (value : Word) : Memory :=
  let expanded := memory.expand (offset + 32)
  { expanded with
    bytes := fun address =>
      if h : offset ≤ address ∧ address < offset + 32 then
        value ⟨address - offset, by omega⟩
      else
        memory.readByte address }

def Memory.copyFrom (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : Memory :=
  let expanded := memory.expand (destOffset + size)
  { expanded with
    bytes := fun address =>
      if _h : destOffset ≤ address ∧ address < destOffset + size then
        source (sourceOffset + (address - destOffset))
      else
        memory.readByte address }

theorem expandedLength_aligned (endOffset : Nat) :
    expandedLength endOffset % 32 = 0 := by
  by_cases h : endOffset = 0
  · simp [expandedLength, h]
  · simp [expandedLength, h]

theorem Memory.expand_size_ge (memory : Memory) (endOffset : Nat) :
    memory.size ≤ (memory.expand endOffset).size := by
  exact Nat.le_max_left _ _

theorem Memory.writeByte_at (memory : Memory) (offset : Nat) (value : Byte) :
    (memory.writeByte offset value).bytes offset = value := by
  simp [Memory.writeByte]

theorem Memory.writeWord_at (memory : Memory) (offset : Nat) (value : Word)
    (index : Fin 32) :
    (memory.writeWord offset value).bytes (offset + index) = value index := by
  simp only [Memory.writeWord]
  split
  · congr
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

theorem Memory.copyFrom_at (memory : Memory) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) (index : Fin size) :
    (memory.copyFrom source destOffset sourceOffset size).bytes (destOffset + index) =
      source (sourceOffset + index) := by
  simp only [Memory.copyFrom]
  split
  · congr
    omega
  · rename_i h
    exact False.elim (h ⟨by omega, by omega⟩)

@[simp] theorem Memory.region_contents (memory : Memory) (offset size : Nat)
    (index : Fin size) :
    (memory.region offset size).contents index = memory.readByte (offset + index) := rfl

/-! ## Operations and their result -/

/-- The byte-memory operations present in generated Yul.  Calldata is total
because EVM zero-extends it; returndata is finite so its copy carries a list
and performs the mandatory bounds check. -/
inductive MemoryOp where
  | mstore (offset : Nat) (value : Word)
  | mload (offset : Nat)
  | mstore8 (offset : Nat) (value : Byte)
  | calldatacopy (destOffset sourceOffset size : Nat) (calldata : Nat → Byte)
  | returndatacopy (destOffset sourceOffset size : Nat) (returndata : List Byte)
  | mcopy (destOffset sourceOffset size : Nat)
  | returndatasize (returndata : List Byte)

inductive Result where
  | ok (memory : Memory)
  | value (value : Nat) (memory : Memory)
  | word (value : Word) (memory : Memory)
  | outOfBounds

def listByte (bytes : List Byte) (offset : Nat) : Byte :=
  bytes.getD offset zeroByte

/-- Denote one non-terminating memory operation. -/
def denoteMemoryOp : MemoryOp → Memory → Result
  | .mstore offset value, memory => .ok (memory.writeWord offset value)
  | .mload offset, memory =>
      let expanded := memory.expand (offset + 32)
      .word (memory.readWord offset) expanded
  | .mstore8 offset value, memory => .ok (memory.writeByte offset value)
  | .calldatacopy dest source size calldata, memory =>
      .ok (memory.copyFrom calldata dest source size)
  | .returndatacopy dest source size returndata, memory =>
      if source + size ≤ returndata.length then
        .ok (memory.copyFrom (listByte returndata) dest source size)
      else
        .outOfBounds
  | .mcopy dest source size, memory =>
      .ok (memory.copyFrom memory.readByte dest source size)
  | .returndatasize returndata, memory => .value returndata.length memory

@[simp] theorem denoteMemoryOp_mstore (memory : Memory) (offset : Nat) (value : Word) :
    denoteMemoryOp (.mstore offset value) memory = .ok (memory.writeWord offset value) := rfl

@[simp] theorem denoteMemoryOp_mload (memory : Memory) (offset : Nat) :
    denoteMemoryOp (.mload offset) memory =
      .word (memory.readWord offset) (memory.expand (offset + 32)) := rfl

@[simp] theorem denoteMemoryOp_mstore8 (memory : Memory) (offset : Nat) (value : Byte) :
    denoteMemoryOp (.mstore8 offset value) memory = .ok (memory.writeByte offset value) := rfl

@[simp] theorem denoteMemoryOp_calldatacopy (memory : Memory) (calldata : Nat → Byte)
    (dest source size : Nat) :
    denoteMemoryOp (.calldatacopy dest source size calldata) memory =
      .ok (memory.copyFrom calldata dest source size) := rfl

theorem denoteMemoryOp_returndatacopy_of_fits (memory : Memory) (returndata : List Byte)
    (dest source size : Nat) (h : source + size ≤ returndata.length) :
    denoteMemoryOp (.returndatacopy dest source size returndata) memory =
      .ok (memory.copyFrom (listByte returndata) dest source size) := by
  simp [denoteMemoryOp, h]

theorem denoteMemoryOp_returndatacopy_of_oob (memory : Memory) (returndata : List Byte)
    (dest source size : Nat) (h : returndata.length < source + size) :
    denoteMemoryOp (.returndatacopy dest source size returndata) memory = .outOfBounds := by
  simp [denoteMemoryOp, Nat.not_le_of_lt h]

@[simp] theorem denoteMemoryOp_mcopy (memory : Memory) (dest source size : Nat) :
    denoteMemoryOp (.mcopy dest source size) memory =
      .ok (memory.copyFrom memory.readByte dest source size) := rfl

/-- `mcopy` reads from the pre-copy snapshot, including when source and
destination overlap. -/
theorem Memory.mcopy_at (memory : Memory) (dest source size : Nat) (index : Fin size) :
    (memory.copyFrom memory.readByte dest source size).bytes (dest + index) =
      memory.readByte (source + index) := by
  exact Memory.copyFrom_at memory memory.readByte dest source size index

@[simp] theorem denoteMemoryOp_returndatasize (memory : Memory) (returndata : List Byte) :
    denoteMemoryOp (.returndatasize returndata) memory = .value returndata.length memory := rfl

/-! ## ABI head/tail representation

The ABI represents a dynamic byte string by a relative pointer in the static
head and a length-prefixed payload in the tail.  Keeping words abstract here
is intentional: byte order belongs to the Yul word encoder, while the layout
and its inverse are independent of that representation. -/

structure AbiDynamicBytes where
  relativeOffset : Word
  lengthWord : Word
  payload : List Byte

structure AbiHeadTail where
  head : Word
  tailLength : Word
  tailPayload : List Byte

def encodeAbiDynamicBytes (value : AbiDynamicBytes) : AbiHeadTail :=
  { head := value.relativeOffset
    tailLength := value.lengthWord
    tailPayload := value.payload }

def decodeAbiDynamicBytes (encoding : AbiHeadTail) : AbiDynamicBytes :=
  { relativeOffset := encoding.head
    lengthWord := encoding.tailLength
    payload := encoding.tailPayload }

@[simp] theorem decode_encode_abiDynamicBytes (value : AbiDynamicBytes) :
    decodeAbiDynamicBytes (encodeAbiDynamicBytes value) = value := by
  cases value
  rfl

@[simp] theorem encode_decode_abiDynamicBytes (encoding : AbiHeadTail) :
    encodeAbiDynamicBytes (decodeAbiDynamicBytes encoding) = encoding := by
  cases encoding
  rfl

/-- Materialize an ABI head/tail value into byte memory.  The payload copy is
last, matching generated Yul and giving it the usual snapshot-free source. -/
def Memory.writeAbiDynamicBytes (memory : Memory) (headOffset tailOffset : Nat)
    (value : AbiDynamicBytes) : Memory :=
  let withHead := memory.writeWord headOffset value.relativeOffset
  let withLength := withHead.writeWord tailOffset value.lengthWord
  withLength.copyFrom (listByte value.payload) (tailOffset + 32) 0 value.payload.length

theorem Memory.writeAbiDynamicBytes_payload (memory : Memory) (headOffset tailOffset : Nat)
    (value : AbiDynamicBytes) (index : Fin value.payload.length) :
    (memory.writeAbiDynamicBytes headOffset tailOffset value).bytes (tailOffset + 32 + index) =
      listByte value.payload index := by
  simpa [Memory.writeAbiDynamicBytes] using
    Memory.copyFrom_at
      ((memory.writeWord headOffset value.relativeOffset).writeWord tailOffset value.lengthWord)
      (listByte value.payload) (tailOffset + 32) 0 value.payload.length index

/-- The canonical dynamic-ABI word decoder used by `Denote` is shared rather
than reimplemented by the byte-memory layer. -/
theorem decodeSupportedParamWord_agrees (ty : ParamType) (word : Nat) :
    Denote.decodeSupportedParamWord ty word = DynamicAbi.decodeSupportedParamWord ty word := rfl

/-! ## Return/revert slices and external-call bridge -/

inductive Termination where
  | returned (data : List Byte)
  | reverted (data : List Byte)
  deriving DecidableEq, Repr

def Memory.slice (memory : Memory) (offset size : Nat) : List Byte :=
  (List.range size).map (fun index => memory.readByte (offset + index))

def denoteReturn (memory : Memory) (offset size : Nat) : Termination :=
  .returned (memory.slice offset size)

def denoteRevert (memory : Memory) (offset size : Nat) : Termination :=
  .reverted (memory.slice offset size)

@[simp] theorem denoteReturn_data (memory : Memory) (offset size : Nat) :
    denoteReturn memory offset size = .returned (memory.slice offset size) := rfl

@[simp] theorem denoteRevert_data (memory : Memory) (offset size : Nat) :
    denoteRevert memory offset size = .reverted (memory.slice offset size) := rfl

/-- A memory layer does not alter call-world rollback.  It refines the Phase
1G failure theorem by pairing the rolled-back call state with byte memory. -/
theorem denoteCall_failure_world_with_memory (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (memory : Memory) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .failure data) :
    ((denoteCall adversary site state).state.world, memory) = (state.world, memory) := by
  rw [denoteCall_failure_world adversary site state data hkind hresult]

/-- The corresponding refinement for an external revert, whose returndata
remains available to a subsequent `returndatacopy`. -/
theorem denoteCall_revert_world_with_memory (adversary : AdversaryModel)
    (site : CallSite) (state : CallState) (memory : Memory) (data : List Nat)
    (hkind : site.kind = .call ∨ site.kind = .delegatecall)
    (hresult : adversary.result site state.world = .revert data) :
    ((denoteCall adversary site state).state.world,
      (denoteCall adversary site state).state.returndata, memory) =
      (state.world, data, memory) := by
  rcases hkind with hkind | hkind <;>
    simp [denoteCall, hkind, hresult, ExternalCallResult.returndata]

/-! ## Soundness against the canonical source memory surface -/

abbrev CanonicalWordMemory := Nat → Verity.Core.Uint256

def canonicalMstore (memory : CanonicalWordMemory) (offset value : Nat) :
    CanonicalWordMemory :=
  fun address => if address = offset then Verity.Core.Uint256.ofNat value else memory address

def canonicalMload (memory : CanonicalWordMemory) (offset : Nat) : Nat :=
  (memory offset).val

theorem canonicalMload_mstore (memory : CanonicalWordMemory) (offset value : Nat) :
    canonicalMload (canonicalMstore memory offset value) offset =
      (Verity.Core.Uint256.ofNat value).val := by
  simp [canonicalMload, canonicalMstore]

/-- Soundness for the source `Stmt.mstore` arm: the canonical statement
denotation is exactly the word update exposed by this module. -/
theorem execStmt_literal_mstore_source_sound
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (offset value : Nat) :
    execStmt oracle fields state (.mstore (.literal offset) (.literal value)) =
      .continue
        { state with
          world :=
            { state.world with
              memory := canonicalMstore state.world.memory
                (wordNormalize offset) (wordNormalize value) } } := by
  simp [execStmt, evalExpr]
  funext address
  simp [canonicalMstore]

/-- Soundness for the corresponding source `Expr.mload` arm. -/
theorem evalExpr_literal_mload_source_sound
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (offset : Nat) :
    evalExpr oracle fields state (.mload (.literal offset)) =
      some (canonicalMload state.world.memory (wordNormalize offset)) := by
  simp [evalExpr, canonicalMload]

end Compiler.CompilationModel.DenoteMemory
