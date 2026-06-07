import Verity.EVM.Uint256
import Verity.EVM.MemoryModel
import Verity.Core.Uint256

namespace Verity.EVM.Frame

open Verity.Core (Uint256)
open Verity.EVM.MemoryModel

/-!
# EVM `CALL` boundary frame conditions

Models the slice of EVM `CALL` semantics that touches the caller's
frame, and proves the frame conditions that downstream contract proofs
need to reason about external calls without quantifying over callee
bytecode.

Promoted from `Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame`.

## What this discharges

Before this module, every benchmark that touched external calls had to
assume (or reproduce in their own file) the EVM-level frame condition
that external `CALL` cannot SSTORE the caller's slots and cannot write
to caller memory outside the declared output buffer. That assumption is
documented in `AXIOMS.md` under "External Call Module". This module
makes the assumption a *theorem* of `Verity.EVM`, parameterised over an
abstract `CalleeResult` whose universal quantification over its
inhabitants is equivalent to quantifying over arbitrary EVM callee
bytecode.

## Roadmap

A subsequent PR will prove that this abstract `CallerFrame` /
`CalleeResult` model is the projection of EvmYul's actual `CALL` opcode
semantics, closing the gap between this layer and the deeper EvmYul
correctness theorems.
-/

/-- An EVM address (160-bit; we expose identity only). -/
abbrev Address := Nat

/-- The caller-side EVM frame at a `CALL` boundary. The four mutable
    sub-states the EVM exposes to a contract are modelled explicitly. -/
structure CallerFrame where
  thisAddress      : Address
  memory           : Nat → Uint256
  storageMap       : Nat → Uint256
  transientStorage : Nat → Uint256
  returnDataBuf    : Nat → Uint256

/-- Everything an arbitrary callee can return to the caller across a
    `CALL` boundary. The callee's internal storage updates are scoped to
    its own address and so do not appear here — they cannot affect the
    caller's frame. Quantifying over inhabitants of this type is
    equivalent to quantifying over arbitrary EVM callee programs that
    produce any `(success, returndata)` pair. -/
structure CalleeResult where
  success           : Uint256
  returnedData      : Nat → Uint256

/-- The portion of EVM `CALL` semantics that touches the caller's frame.

By the Yellow Paper, `CALL` to a target ≠ self with the caller's output
buffer `[outOff, outOff + outSize)` updates the caller's memory by
copying `outSize` words of the callee's returndata into that range,
leaves storage and transient storage untouched, and writes the new
returndata buffer to the caller's `returnDataBuf`. -/
def applyCallToCaller
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    : CallerFrame :=
  { caller with
      memory := fun i =>
        if outOff ≤ i ∧ i < outOff + outSize then
          callee.returnedData (i - outOff)
        else
          caller.memory i
      returnDataBuf := callee.returnedData }

/-! ## Single-CALL frame theorems -/

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

theorem external_call_preserves_caller_memory_outside_output_buffer
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat) (hOutside : ¬ (outOff ≤ i ∧ i < outOff + outSize)) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i := by
  simp [applyCallToCaller, hOutside]

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
