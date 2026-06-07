import Verity.EVM.MemoryModel

namespace Verity.EVM.Layout

open Verity.EVM.MemoryModel

/-!
# Solc memory-layout schema

A reusable schema for the standard Solidity memory layout, plus a small
proof toolkit for discharging disjointness goals about call-output
buffers and heap regions.

Promoted from
`Benchmark.Cases.ERC4337.EntryPointInvariant.Layout.SolcLayout`.

## Standard solc memory layout

* Bytes `0x00..0x3f` (words 0-1): scratch space, ephemeral. Used as the
  hash input and as the output buffer for keccak / external `call`.
* Byte `0x40` (word 2): free memory pointer. Reads give the first free
  heap offset.
* Byte `0x60` (word 3): the zero slot. Read-only, always zero.
* Bytes `0x80+` (words 4+): heap. `new T[](n)` allocates here.

This is documented at
<https://docs.soliditylang.org/en/latest/internals/layout_in_memory.html>.

## `solc_disjoint` tactic shape

We expose the disjointness theorem `call_buffer_disjoint_from_heap`
that discharges the `MemoryModel.Disjoint` goal whenever the call buffer
sits inside the scratch range and the target region sits in the heap.
For contracts that follow the standard layout this is the only
disjointness fact needed; downstream proofs invoke this lemma directly.
A `solc_disjoint` Lean tactic is the next refinement step (tracked in
`docs/ROADMAP.md`).
-/

/-- The standard solc memory layout, expressed in word offsets. -/
structure SolcLayout where
  scratchLo  : Nat
  scratchHi  : Nat
  fmpSlotIdx : Nat
  zeroSlotIdx : Nat
  heapStart  : Nat
  heapRegionBase : Nat
  heapRegionWords : Nat
  scratchLo_lt_hi     : scratchLo < scratchHi
  scratchHi_le_fmp    : scratchHi ≤ fmpSlotIdx
  fmpSlotIdx_lt_zero  : fmpSlotIdx < zeroSlotIdx
  zeroSlot_lt_heap    : zeroSlotIdx < heapStart
  heap_le_heapBase    : heapStart ≤ heapRegionBase
  heapRegionWords_pos : 0 < heapRegionWords

/-- The canonical solc layout: scratch at words 0-1, FMP at word 2,
    zero slot at word 3, heap from word 4. -/
def canonicalSolcLayout (heapRegionBase heapRegionWords : Nat)
    (hHeap : 4 ≤ heapRegionBase) (hPos : 0 < heapRegionWords) : SolcLayout :=
  { scratchLo := 0
    scratchHi := 2
    fmpSlotIdx := 2
    zeroSlotIdx := 3
    heapStart := 4
    heapRegionBase
    heapRegionWords
    scratchLo_lt_hi     := by decide
    scratchHi_le_fmp    := by decide
    fmpSlotIdx_lt_zero  := by decide
    zeroSlot_lt_heap    := by decide
    heap_le_heapBase    := hHeap
    heapRegionWords_pos := hPos }

/-- A call site that uses the scratch range as its output buffer. -/
structure ScratchOutputBuffer (L : SolcLayout) where
  outOff   : Nat
  outSize  : Nat
  outOff_eq_scratchLo : outOff = L.scratchLo
  outSize_in_range    : outOff + outSize ≤ L.scratchHi

/-- **The disjointness theorem**: any call site that uses the scratch
    range as output buffer cannot disturb any word in the heap region
    declared by `SolcLayout`. -/
theorem call_buffer_disjoint_from_heap
    (L : SolcLayout) (S : ScratchOutputBuffer L) :
    S.outOff + S.outSize ≤ L.heapRegionBase ∨
    L.heapRegionBase + L.heapRegionWords ≤ S.outOff := by
  left
  have h1 := S.outSize_in_range
  have h2 := L.scratchHi_le_fmp
  have h3 := L.fmpSlotIdx_lt_zero
  have h4 := L.zeroSlot_lt_heap
  have h5 := L.heap_le_heapBase
  omega

/-- The same disjointness in `MemoryModel.Disjoint` form, ready to
    compose with the frame theorems in `Verity.EVM.Frame`. -/
theorem call_buffer_disjoint_from_heap_memmodel
    (L : SolcLayout) (S : ScratchOutputBuffer L) :
    Disjoint S.outOff (S.outOff + S.outSize)
             L.heapRegionBase (L.heapRegionBase + L.heapRegionWords) := by
  unfold Disjoint
  exact call_buffer_disjoint_from_heap L S

end Verity.EVM.Layout
