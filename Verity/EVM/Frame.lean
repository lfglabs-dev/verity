import Verity.EVM.Uint256
import Verity.EVM.MemoryModel
import Verity.Core.Uint256

namespace Verity.EVM.Frame

open Verity.Core (Uint256)
open Verity.EVM.MemoryModel

/-!
# EVM `CALL` boundary frame conditions

Models the slice of EVM `CALL`/returndata behaviour that touches the
caller frame, and proves the frame conditions that downstream contract
proofs need to reason about caller-local observables without quantifying
over callee bytecode.

Promoted from `Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame`.

## What this discharges

This module is frame-level groundwork only. It does not prove that any
compiler lowering, EvmYul opcode semantics, ECM shim, foreign call, or
low-level call is supported end-to-end. In particular, it intentionally
does not remove the external-call blockers in `SupportedSpec`.

Before this module, every benchmark that touched external calls had to
assume (or reproduce in their own file) the EVM-level frame condition
that external `CALL` cannot SSTORE the caller's slots and cannot write
to caller memory outside the declared output buffer. That assumption is
documented in `AXIOMS.md` under "External Call Module". This module
makes the frame condition a theorem of `Verity.EVM`, parameterised over
an abstract finite `CalleeResult` observable.

## Roadmap

A subsequent PR will prove that this abstract `CallerFrame` /
`CalleeResult` model is the projection of EvmYul's actual `CALL` opcode
semantics, closing the gap between this layer and the deeper EvmYul
correctness theorems.
-/

/-- An EVM address (160-bit; we expose identity only). -/
abbrev Address := Nat

/-- Finite, word-addressed returndata observable.

`size` is measured in this module's abstract word units, matching the
word-addressed memory model used by `Verity.EVM.MemoryModel`. The
`wordAt` is indexed by `Fin size`, so returndata cannot be observed
outside its finite payload. -/
structure ReturnData where
  size   : Nat
  wordAt : Fin size → Uint256

namespace ReturnData

/-- Bounds-checked word lookup for a finite returndata payload. -/
def lookup (data : ReturnData) (idx : Fin data.size) : Uint256 :=
  data.wordAt idx

theorem lookup_eq_wordAt (data : ReturnData) (idx : Fin data.size) :
    data.lookup idx = data.wordAt idx := rfl

end ReturnData

/-- The caller-side EVM frame at a `CALL` boundary. The four mutable
    sub-states the EVM exposes to a contract are modelled explicitly. -/
structure CallerFrame where
  thisAddress      : Address
  memory           : Nat → Uint256
  storageMap       : Nat → Uint256
  transientStorage : Nat → Uint256
  returnDataBuf    : ReturnData

/-- Everything an arbitrary callee can return to the caller across a
    `CALL` boundary. The callee's internal storage updates are scoped to
    its own address and so do not appear here — they cannot affect the
    caller's frame. This finite observable deliberately stops at the
    caller-frame boundary; it is not a proof of full external-call
    correctness. -/
structure CalleeResult where
  success           : Uint256
  returnedData      : ReturnData

/-- Number of returndata words copied into the caller's declared output
    buffer by this frame-level model. -/
def callOutputCopySize (outSize : Nat) (callee : CalleeResult) : Nat :=
  Nat.min outSize callee.returnedData.size

theorem callOutputCopySize_le_outSize
    (outSize : Nat) (callee : CalleeResult) :
    callOutputCopySize outSize callee ≤ outSize := by
  exact Nat.min_le_left outSize callee.returnedData.size

theorem callOutputCopySize_le_returnedDataSize
    (outSize : Nat) (callee : CalleeResult) :
    callOutputCopySize outSize callee ≤ callee.returnedData.size := by
  exact Nat.min_le_right outSize callee.returnedData.size

/-- The portion of EVM `CALL` semantics that touches the caller's frame.

By the Yellow Paper, `CALL` to a target ≠ self with the caller's output
buffer `[outOff, outOff + outSize)` updates the caller's memory by copying
the finite callee returndata prefix that fits in that range, leaves
storage and transient storage untouched, and writes the new returndata
buffer to the caller's `returnDataBuf`.

Frame-level groundwork only: this is a pure observable API, not a full
external-call correctness theorem. -/
def applyCallToCaller
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    : CallerFrame :=
  { caller with
      memory := fun i =>
        if outOff ≤ i ∧ i < outOff + callOutputCopySize outSize callee then
          callee.returnedData.wordAt ⟨i - outOff, by
            have hCopySize := callOutputCopySize_le_returnedDataSize outSize callee
            omega⟩
        else
          caller.memory i
      returnDataBuf := callee.returnedData }

/-- The frame-level observable returned by applying an external-call result
    to the caller frame. The `success` field is the callee success observable;
    the `frame` field is the caller frame after applying caller-local effects. -/
structure CallTransition where
  success : Uint256
  frame   : CallerFrame

/-- Apply an abstract external-call result to the caller frame while keeping
    the callee success bit as a separate observable. This is frame-level
    groundwork only, not an EvmYul/ABI external-call support theorem. -/
def applyCallResultToCaller
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    : CallTransition :=
  { success := callee.success
    frame := applyCallToCaller caller outOff outSize callee }

/-- Size of the current finite returndata payload in abstract words. -/
def returndataSize (caller : CallerFrame) : Nat :=
  caller.returnDataBuf.size

/-- Bounds-checked word lookup in the current finite returndata payload. -/
def returndataWord (caller : CallerFrame) (idx : Fin (returndataSize caller)) : Uint256 :=
  caller.returnDataBuf.lookup idx

/-- Bounded `RETURNDATACOPY` at the caller-frame level.

The proof argument records the EVM bounds check (`src + len` is within
the current finite returndata payload). The transition only mutates the
destination memory range `[dst, dst + len)`. -/
def boundedReturndataCopy
    (caller : CallerFrame) (dst src len : Nat)
    (_hBound : src + len ≤ returndataSize caller) : CallerFrame :=
  { caller with
      memory := fun i =>
        if dst ≤ i ∧ i < dst + len then
          caller.returnDataBuf.wordAt ⟨src + (i - dst), by
            change src + len ≤ caller.returnDataBuf.size at _hBound
            omega⟩
        else
          caller.memory i }

/-- Result of frame-level `revertReturndata`: the revert payload plus the
    unmodified caller frame. -/
structure RevertReturndataResult where
  payload : ReturnData
  frame   : CallerFrame

/-- Revert with the current returndata payload without mutating the caller
    frame. This is a caller-frame observable helper only. -/
def revertReturndata (caller : CallerFrame) : RevertReturndataResult :=
  { payload := caller.returnDataBuf
    frame := caller }

/-! ## Single-CALL frame-level groundwork theorems -/

theorem frame_groundwork_call_transition_exposes_callee_success
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult) :
    (applyCallResultToCaller caller outOff outSize callee).success =
      callee.success := rfl

theorem frame_groundwork_call_transition_frame_eq_applyCallToCaller
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult) :
    (applyCallResultToCaller caller outOff outSize callee).frame =
      applyCallToCaller caller outOff outSize callee := rfl

theorem external_call_preserves_caller_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).storageMap slotIdx =
      caller.storageMap slotIdx := by
  simp [applyCallToCaller]

theorem external_call_preserves_caller_transient_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).transientStorage slotIdx =
      caller.transientStorage slotIdx := by
  simp [applyCallToCaller]

theorem external_call_preserves_caller_memory_outside_copied_output
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat)
    (hOutside : ¬ (outOff ≤ i ∧ i < outOff + callOutputCopySize outSize callee)) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  simp [applyCallToCaller, hOutside]

theorem external_call_preserves_caller_memory_outside_output_buffer
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat) (hOutside : ¬ (outOff ≤ i ∧ i < outOff + outSize)) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  apply external_call_preserves_caller_memory_outside_copied_output
  intro hIn
  apply hOutside
  have hLe := callOutputCopySize_le_outSize outSize callee
  exact ⟨hIn.1, by omega⟩

theorem external_call_copies_returnData_word
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat)
    (hIn : outOff ≤ i ∧ i < outOff + callOutputCopySize outSize callee) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      callee.returnedData.wordAt ⟨i - outOff, by
        have hCopySize := callOutputCopySize_le_returnedDataSize outSize callee
        omega⟩ := by
  simp [applyCallToCaller, hIn]

/-- Headline form: caller-memory preservation under a disjoint output
    buffer. Composes directly with `MemoryModel.Disjoint`. -/
theorem external_call_preserves_caller_memory
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (regionLo regionHi : Nat)
    (hDisj : outOff + outSize ≤ regionLo ∨ regionHi ≤ outOff)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  apply external_call_preserves_caller_memory_outside_output_buffer
  rintro ⟨h1, h2⟩
  rcases hDisj with h | h <;> omega

theorem external_call_returnDataBuf_eq_callee_result
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult) :
    (applyCallToCaller caller outOff outSize callee).returnDataBuf =
      callee.returnedData := rfl

theorem external_call_returndataSize_eq_callee_result
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult) :
    returndataSize (applyCallToCaller caller outOff outSize callee) =
      callee.returnedData.size := rfl

theorem external_call_returndataWord_eq_callee_result
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (idx : Fin callee.returnedData.size) :
    returndataWord (applyCallToCaller caller outOff outSize callee) idx =
      callee.returnedData.wordAt idx := rfl

/-! ## Bounded `RETURNDATACOPY` frame-level groundwork theorems -/

theorem bounded_returndataCopy_preserves_caller_storage
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller) (slotIdx : Nat) :
    (boundedReturndataCopy caller dst src len hBound).storageMap slotIdx =
      caller.storageMap slotIdx := by
  simp [boundedReturndataCopy]

theorem bounded_returndataCopy_preserves_caller_transient_storage
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller) (slotIdx : Nat) :
    (boundedReturndataCopy caller dst src len hBound).transientStorage slotIdx =
      caller.transientStorage slotIdx := by
  simp [boundedReturndataCopy]

theorem bounded_returndataCopy_preserves_returnDataBuf
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller) :
    (boundedReturndataCopy caller dst src len hBound).returnDataBuf =
      caller.returnDataBuf := rfl

theorem bounded_returndataCopy_preserves_returndataSize
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller) :
    returndataSize (boundedReturndataCopy caller dst src len hBound) =
      returndataSize caller := rfl

theorem bounded_returndataCopy_preserves_caller_memory_outside_copy_range
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller)
    (i : Nat) (hOutside : ¬ (dst ≤ i ∧ i < dst + len)) :
    (boundedReturndataCopy caller dst src len hBound).memory i =
      caller.memory i := by
  simp [boundedReturndataCopy, hOutside]

theorem bounded_returndataCopy_copies_current_returnData_word
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller)
    (i : Nat) (hIn : dst ≤ i ∧ i < dst + len) :
    (boundedReturndataCopy caller dst src len hBound).memory i =
      caller.returnDataBuf.wordAt ⟨src + (i - dst), by
        change src + len ≤ caller.returnDataBuf.size at hBound
        omega⟩ := by
  simp [boundedReturndataCopy, hIn]

theorem bounded_returndataCopy_source_index_lt_returndataSize
    (caller : CallerFrame) (dst src len : Nat)
    (hBound : src + len ≤ returndataSize caller)
    (i : Nat) (hIn : dst ≤ i ∧ i < dst + len) :
    src + (i - dst) < returndataSize caller := by
  have hRel : i - dst < len := by omega
  omega

/-! ## `revertReturndata` frame-level groundwork theorems -/

theorem revertReturndata_returns_current_payload
    (caller : CallerFrame) :
    (revertReturndata caller).payload = caller.returnDataBuf := rfl

theorem revertReturndata_returns_current_payload_size
    (caller : CallerFrame) :
    (revertReturndata caller).payload.size = returndataSize caller := rfl

theorem revertReturndata_returns_current_payload_word
    (caller : CallerFrame) (idx : Fin caller.returnDataBuf.size) :
    (revertReturndata caller).payload.wordAt idx =
      caller.returnDataBuf.wordAt idx := rfl

theorem revertReturndata_does_not_mutate_caller_frame
    (caller : CallerFrame) :
    (revertReturndata caller).frame = caller := rfl

theorem revertReturndata_preserves_caller_memory
    (caller : CallerFrame) (idx : Nat) :
    (revertReturndata caller).frame.memory idx = caller.memory idx := rfl

theorem revertReturndata_preserves_caller_storage
    (caller : CallerFrame) (slotIdx : Nat) :
    (revertReturndata caller).frame.storageMap slotIdx =
      caller.storageMap slotIdx := rfl

theorem revertReturndata_preserves_caller_transient_storage
    (caller : CallerFrame) (slotIdx : Nat) :
    (revertReturndata caller).frame.transientStorage slotIdx =
      caller.transientStorage slotIdx := rfl

/-! ## Iterated-CALL frame theorems -/

theorem external_calls_preserve_caller_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).storageMap slotIdx =
    caller.storageMap slotIdx := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_storage caller c.1 c.2.1 c.2.2 slotIdx
    have := ih (applyCallToCaller caller c.1 c.2.1 c.2.2)
    simp [List.foldl]; rw [this, hStep]

theorem external_calls_preserve_caller_transient_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).transientStorage slotIdx =
    caller.transientStorage slotIdx := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_transient_storage
      caller c.1 c.2.1 c.2.2 slotIdx
    have := ih (applyCallToCaller caller c.1 c.2.1 c.2.2)
    simp [List.foldl]; rw [this, hStep]

theorem external_calls_preserve_caller_memory_in_disjoint_region
    (caller : CallerFrame)
    (regionLo regionHi : Nat)
    (calls : List (Nat × Nat × CalleeResult))
    (hAllDisj : ∀ c ∈ calls,
      c.1 + c.2.1 ≤ regionLo ∨ regionHi ≤ c.1)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).memory i =
    caller.memory i := by
  induction calls generalizing caller with
  | nil => rfl
  | cons c rest ih =>
    have hStep := external_call_preserves_caller_memory caller c.1 c.2.1 c.2.2
      regionLo regionHi (hAllDisj c (List.mem_cons_self ..)) i hLo hHi
    have hRest : ∀ d ∈ rest, d.1 + d.2.1 ≤ regionLo ∨ regionHi ≤ d.1 := by
      intro d hd; exact hAllDisj d (List.mem_cons_of_mem _ hd)
    have hIH := ih (applyCallToCaller caller c.1 c.2.1 c.2.2) hRest
    simp [List.foldl]; rw [hIH, hStep]

end Verity.EVM.Frame
