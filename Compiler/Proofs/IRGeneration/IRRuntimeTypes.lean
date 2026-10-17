import Verity.Core.Model.ExecutionContext
import Compiler.Proofs.IRGeneration.IRStorageWord
import Verity.Core.ByteMemory
import Verity.Core.Model.PhysicalCopy

open Compiler.CompilationModel
open Compiler.CompilationModel.DenoteMemory
open Verity.Core

namespace Compiler.Proofs.IRGeneration

/-- Proof-side execution state shared by IR semantics and native-runtime harnesses. -/
structure IRState where
  /-- Actual REVERT memory slice; none for an unclassified interpreter failure. -/
  observedRevert : Option (Nat × Nat) := none
  /-- Canonical account/world carrier for creation-capable execution. This is
      mandatory when creation is reached: no empty account map is synthesized.
      The local storage/memory observations must be synchronized at the opcode
      boundary; this field alone is not an execution or coherence certificate. -/
  creationWorld : Option Verity.ContractState := none
  /-- Actual ephemeral context when provided by a metered executor. Missing
      context cannot authorize creation or supply a guessed gas allowance. -/
  executionContext : Option Verity.Core.Model.ExecutionContext := none
  /-- Variable bindings (name -> value). -/
  vars : List (String × Nat)
  /-- Storage slots (slot -> value).

      Typed via `IRStorageWord` so the proof surface tracks the bounded EVM
      storage carrier. -/
  storage : IRStorageSlot → IRStorageWord
  /-- Transient storage slots (slot -> value). -/
  transientStorage : Nat → Nat := fun _ => 0
  /-- Memory words (offset -> value). -/
  memory : Nat → Nat
  /-- Physical byte-backed memory carrier.  The word view above is kept as an
      executable compatibility projection until all IR proofs have migrated. -/
  byteMemory : Memory := Memory.empty
  /-- Calldata words. -/
  calldata : List Nat
  /-- Return value, if any. -/
  returnValue : Option Nat
  /-- Sender address. -/
  sender : Nat
  /-- Msg.value seen by `callvalue()`. -/
  msgValue : Nat := 0
  /-- Contract address seen by `address()`. -/
  thisAddress : Nat := 0
  /-- Block timestamp seen by `timestamp()`. -/
  blockTimestamp : Nat := 0
  /-- Block number seen by `number()`. -/
  blockNumber : Nat := 0
  /-- Chain id seen by `chainid()`. -/
  chainId : Nat := 0
  /-- Blob base fee seen by `blobbasefee()`. -/
  blobBaseFee : Nat := 0
  /-- tx.origin seen by `origin()`. -/
  txOrigin : Nat := 0
  /-- Function selector. -/
  selector : Nat
  /-- Emitted log records for this execution. -/
  events : List (List Nat) := []
  /-- EXTCODESIZE at address (environment read, no state mutation). -/
  codeSize : Nat → Nat := fun _ => 0
  /-- EIP-211 returndata buffer, as 32-byte words. -/
  returndata : List Nat := []
  deriving Nonempty

/-- Initial state for IR execution. -/
def IRState.initial (sender : Nat) : IRState :=
  { vars := []
    storage := fun _ => 0
    transientStorage := fun _ => 0
    memory := fun _ => 0
    calldata := []
    returnValue := none
    sender := sender
    msgValue := 0
    thisAddress := 0
    blockTimestamp := 0
    blockNumber := 0
    chainId := 0
    blobBaseFee := 0
    txOrigin := 0
    selector := 0
    events := [] }

/-- Capture the actual REVERT operands without fabricating an empty payload for
an interpreter failure. Bytes are read from this state's physical carrier. -/
def IRState.captureRevert (state : IRState) (offset size : Nat) : IRState :=
  { state with observedRevert := some (offset, size) }

def IRState.revertBytes (state : IRState) : Option (List UInt8) :=
  state.observedRevert.map (fun (offset, size) =>
    (List.range size).map (fun index => UInt8.ofNat (state.byteMemory.readByte (offset + index)).val))

@[simp] theorem IRState.captureRevert_observed (state : IRState) (offset size : Nat) :
    (state.captureRevert offset size).observedRevert = some (offset, size) := rfl

@[simp] theorem IRState.captureRevert_storage (state : IRState) (offset size : Nat) :
    (state.captureRevert offset size).storage = state.storage := rfl

@[simp] theorem IRState.captureRevert_memory (state : IRState) (offset size : Nat) :
    (state.captureRevert offset size).byteMemory = state.byteMemory := rfl

/-- Exact EVM `mstore` update for the IR state.  The legacy word view is
    recomputed from the byte carrier, so overlapping and unaligned reads are
    represented without approximation. -/
def IRState.installPhysicalMemory (state : IRState) (physical : Memory) : IRState :=
  { state with
      byteMemory := physical
      memory := fun query => (wordValue (physical.readWord query)).val }

def IRState.writePhysicalMemoryValue (state : IRState) (offset value : Nat) : IRState :=
  state.installPhysicalMemory
    (state.byteMemory.writeWord offset (valueWord (Uint256.ofNat value)))

/-- Exact opcode copy; a zero extent preserves the complete state even when
its legacy word map and byte carrier were not coherent. -/
def IRState.copyPhysicalBytes (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) : IRState :=
  if size = 0 then state else
    state.installPhysicalMemory (state.byteMemory.copyFrom source destOffset sourceOffset size)

def IRState.copyPhysicalCalldata (state : IRState) (destOffset sourceOffset size : Nat) : IRState :=
  state.copyPhysicalBytes (calldataPhysicalByte state.selector state.calldata) destOffset sourceOffset size

def IRState.copyPhysicalReturndata (state : IRState) (destOffset sourceOffset size : Nat) : IRState :=
  state.copyPhysicalBytes (wordListByte state.returndata) destOffset sourceOffset size

@[simp] theorem IRState.copyPhysicalBytes_zero (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset : Nat) :
    state.copyPhysicalBytes source destOffset sourceOffset 0 = state := rfl

theorem IRState.copyPhysicalBytes_byteMemory (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    (state.copyPhysicalBytes source destOffset sourceOffset size).byteMemory =
      state.byteMemory.copyFrom source destOffset sourceOffset size := by
  by_cases zero : size = 0
  · simp only [zero, copyPhysicalBytes_zero, Memory.copyFrom_zero]
  · simp only [copyPhysicalBytes, zero, if_false]
    rfl

/-- Complete frame, erasing only the byte carrier and its word observation. -/
theorem IRState.copyPhysicalBytes_frame (state : IRState) (source : Nat → Byte)
    (destOffset sourceOffset size : Nat) :
    (state.copyPhysicalBytes source destOffset sourceOffset size).installPhysicalMemory Memory.empty =
      state.installPhysicalMemory Memory.empty := by
  by_cases zero : size = 0
  · simp only [copyPhysicalBytes, zero, if_true]
  · simp only [copyPhysicalBytes, zero, if_false]
    rfl

@[simp] theorem IRState.writePhysicalMemoryValue_at (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).memory offset = (Uint256.ofNat value).val := by
  change (wordValue ((state.byteMemory.writeWord offset
    (valueWord (Uint256.ofNat value))).readWord offset)).val = _
  rw [Memory.readWord_writeWord_at, wordValue_valueWord]

@[simp] theorem IRState.writePhysicalMemoryValue_storage (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).storage = state.storage := rfl

@[simp] theorem IRState.writePhysicalMemoryValue_events (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).events = state.events := rfl

@[simp] theorem IRState.writePhysicalMemoryValue_vars (state : IRState) (offset value : Nat) :
    (state.writePhysicalMemoryValue offset value).vars = state.vars := rfl

/-- Lookup variable in state. -/
def IRState.getVar (s : IRState) (name : String) : Option Nat :=
  s.vars.find? (·.1 == name) |>.map (·.2)

/-- Set variable in state. -/
def IRState.setVar (s : IRState) (name : String) (value : Nat) : IRState :=
  { s with vars := (name, value) :: s.vars.filter (·.1 != name) }

/-- Set several variables in order, matching left-to-right binding behavior. -/
def IRState.setVars (s : IRState) (bindings : List (String × Nat)) : IRState :=
  bindings.foldl (fun st (name, value) => st.setVar name value) s

/-- Proof-side transaction context shared by IR and native-runtime harnesses. -/
structure IRTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  txOrigin : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Proof-side observable execution result shared by IR and native-runtime harnesses. -/
structure IRResult where
  /-- Interpreter refusal is not a certified EVM failure. -/
  interpretationError : Option String := none
  /-- Actual terminal exceptional context, distinct from REVERT bytes. -/
  exceptionalContext : Option Verity.Core.Model.ExecutionContext := none
  /-- None denotes no certified REVERT payload, rather than fabricated empty bytes. -/
  revertData : Option (List UInt8) := none
  success : Bool
  returnValue : Option Nat
  finalStorage : IRStorageSlot → IRStorageWord
  finalMappings : Nat → Nat → IRStorageWord
  events : List (List Nat)

end Compiler.Proofs.IRGeneration
