import Verity.EVM.Uint256
import Verity.Core.Uint256

namespace Verity.EVM.MemoryModel

open Verity.Core (Uint256)

/-!
# Abstract EVM memory model

A word-addressed model of EVM memory used by the `CALL` boundary frame
proofs in `Verity.EVM.Frame`. The model is deliberately abstract — it
quantifies over the callee's returndata function without bottoming out
in EvmYul semantics — so that downstream contract proofs can compose
frame conditions without paying for the full EvmYul model.

Promoted from `Benchmark.Cases.ERC4337.EntryPointInvariant.Frame.MemFrame`.

## Roadmap

A future PR will prove that this abstract model is the projection of
EvmYul's memory semantics through the `CALL` opcode, closing the trust
gap between Verity's contract-level model and EvmYul.
-/

/-- A word-addressed EVM memory region. -/
abbrev MemState := Nat → Uint256

/-- Read a word at the given offset. -/
def myMload (m : MemState) (off : Nat) : Uint256 := m off

/-- Write a word at the given offset; other offsets unchanged. -/
def myMstore (m : MemState) (off : Nat) (v : Uint256) : MemState :=
  fun i => if i = off then v else m i

/-- Model of a `CALL` that writes `outSize` words of returndata into the
    caller's memory starting at `outOff`. The `returnedData` argument is
    the universal-quantification surface for arbitrary callee bytecode:
    every word the callee can possibly return appears here. -/
def callWithReturnBuffer
    (m : MemState) (outOff outSize : Nat) (returnedData : Nat → Uint256) : MemState :=
  fun i => if outOff ≤ i ∧ i < outOff + outSize then returnedData (i - outOff)
           else m i

/-- Two half-open ranges are disjoint. -/
def Disjoint (lo1 hi1 lo2 hi2 : Nat) : Prop :=
  hi1 ≤ lo2 ∨ hi2 ≤ lo1

/-- A CALL with output buffer `[outOff, outOff+outSize)` preserves every
    word in a disjoint region `[regionLo, regionHi)`. -/
theorem call_preserves_disjoint_region
    (m : MemState) (outOff outSize regionLo regionHi : Nat)
    (returnedData : Nat → Uint256)
    (hDisj : Disjoint outOff (outOff + outSize) regionLo regionHi)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (callWithReturnBuffer m outOff outSize returnedData) i = m i := by
  unfold callWithReturnBuffer
  by_cases hIn : outOff ≤ i ∧ i < outOff + outSize
  · rcases hDisj with h | h <;> omega
  · simp [hIn]

/-- Iterated non-aliasing: a sequence of CALLs with all output buffers
    disjoint from the target region preserves the region pointwise. -/
theorem repeated_calls_preserve_region
    (m : MemState) (regionLo regionHi : Nat) (i : Nat)
    (hLo : regionLo ≤ i) (hHi : i < regionHi)
    (calls : List (Nat × Nat × (Nat → Uint256)))
    (hAllDisj : ∀ c ∈ calls,
      Disjoint c.1 (c.1 + c.2.1) regionLo regionHi) :
    (calls.foldl (fun acc c => callWithReturnBuffer acc c.1 c.2.1 c.2.2) m) i = m i := by
  induction calls generalizing m with
  | nil => rfl
  | cons c rest ih =>
    have hcDisj : Disjoint c.1 (c.1 + c.2.1) regionLo regionHi :=
      hAllDisj c (List.mem_cons_self ..)
    have hRestDisj : ∀ d ∈ rest,
        Disjoint d.1 (d.1 + d.2.1) regionLo regionHi := by
      intro d hd; exact hAllDisj d (List.mem_cons_of_mem _ hd)
    have hStep := call_preserves_disjoint_region m c.1 c.2.1 regionLo regionHi
      c.2.2 hcDisj i hLo hHi
    have hIh := ih (callWithReturnBuffer m c.1 c.2.1 c.2.2) hRestDisj
    simp [List.foldl]
    rw [hIh]; exact hStep

/-- The headline aliasing theorem: if a word is written to memory before a
    CALL with a disjoint output buffer, reading the same word after the
    CALL yields the originally written value, regardless of the callee's
    returndata. -/
theorem memory_frame_under_arbitrary_callee
    (regionLo regionHi outOff outSize : Nat)
    (hDisj : Disjoint outOff (outOff + outSize) regionLo regionHi)
    (m₀ : MemState) (writtenValue : Uint256) (i : Nat)
    (hLo : regionLo ≤ i) (hHi : i < regionHi)
    (returnedData : Nat → Uint256) :
    let mAfterWrite := myMstore m₀ i writtenValue
    let mAfterCall := callWithReturnBuffer mAfterWrite outOff outSize returnedData
    myMload mAfterCall i = writtenValue := by
  unfold myMload myMstore callWithReturnBuffer
  by_cases hIn : outOff ≤ i ∧ i < outOff + outSize
  · rcases hDisj with h | h <;> omega
  · simp [hIn]

end Verity.EVM.MemoryModel
