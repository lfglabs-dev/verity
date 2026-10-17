import Verity.Core.ByteMemory
import Verity.Core.Model.DenoteExternalCalls

/-!
# Dynamic memory, bytes, and ABI denotation

This module is the byte-precise memory layer of the canonical denotation.  It
models the operations emitted by Verity's Yul lowering: `mstore`, `mload`,
`mstore8`, `calldatacopy`, `returndatacopy`, `returndatasize`, `return`, and
`revert`.  Memory is zero-filled and expands in 32-byte words through the
highest byte touched, exactly as EVM memory does.  `returndatacopy` is the only
operation in this slice that can fail: unlike calldata, returndata is not
zero-extended.

`mcopy`, `codecopy`, and `extcodecopy` are out of scope: the compiler does not
emit them for the supported source fragment.  Gas accounting and the EVM's
address-space limit are also deliberately outside the canonical functional
model.

Canonical `Denote` installs physical bytes and every overlapping word view
together. The final section links literal source stores to the complete
physical poststate. The isolated word-map helpers are retained as abstract
single-cell layout operations, not descriptions of canonical execution.
-/

namespace Compiler.CompilationModel.DenoteMemory

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.CompilationModel.DenoteExternalCalls

/-! Byte, Word, Memory, expansion, stores, copies and their universal lemmas
are imported from the shared core. This module must not redeclare them. -/

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

@[simp] theorem denoteMemoryOp_returndatasize (memory : Memory) (returndata : List Byte) :
    denoteMemoryOp (.returndatasize returndata) memory = .value returndata.length memory := rfl

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

/-- Exact complete-world soundness for the source `Stmt.mstore` arm,
including physical bytes and every overlapping word observation. -/
theorem execStmt_literal_mstore_source_sound
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (offset value : Nat) :
    execStmt oracle fields state (.mstore (.literal offset) (.literal value)) =
      .continue
        { state with
          world := state.world.writePhysicalMemoryValue
            (wordNormalize offset) (Verity.Core.Uint256.ofNat (wordNormalize value)) } := by
  simp only [execStmt, evalExpr]

/-- The physical write retains the original same-offset word readback, while
also representing its effect on unaligned and overlapping reads. -/
theorem physicalMload_mstore (world : Verity.ContractState) (offset value : Nat) :
    canonicalMload
      (world.writePhysicalMemoryValue (wordNormalize offset)
        (Verity.Core.Uint256.ofNat (wordNormalize value))).memory
      (wordNormalize offset) =
      (Verity.Core.Uint256.ofNat (wordNormalize value)).val := by
  unfold canonicalMload
  rw [Compiler.CompilationModel.PhysicalMemory.writePhysicalMemoryValue_at]

/-- Soundness for the corresponding source `Expr.mload` arm. -/
theorem evalExpr_literal_mload_source_sound
    (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (offset : Nat) :
    evalExpr oracle fields state (.mload (.literal offset)) =
      some (canonicalMload state.world.memory (wordNormalize offset)) := by
  simp [evalExpr, canonicalMload]

end Compiler.CompilationModel.DenoteMemory
