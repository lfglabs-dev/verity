/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.Proofs.PackedBitfieldMetaSpec
import Compiler.Proofs.MetaSpecs

namespace Compiler.Proofs.SlotCoalescingShim

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.PackedBitfieldMetaSpec
open Compiler.Proofs.MetaSpecs

/-!
# Verified Automatic Packed-Slot Coalescing Shim (`SLOAD`/`SSTORE` Fusion, Phase 4 Track P3)

This module formalizes and verifies the compiler optimization pass that coalesces a
sequence of $N$ sub-word bitfield writes `(lens₁, v₁), …, (lensₙ, vₙ)` targeting the
same 256-bit EVM storage slot `s` (such as Uniswap v3/v4 `Slot0` packing
`sqrtPriceX96` [160b], `tick` [24b], `protocolFee` [24b], and `lpFee` [24b]) from:

- **Uncoalesced Execution (`execUncoalescedPackedWrites`)**:
  $N$ sequential `(SLOAD s; setBits; SSTORE s)` pairs, costing $N \times 200$ warm gas, to
- **Coalesced Execution (`execCoalescedPackedWrites`)**:
  **1 `SLOAD s`** + in-register composition of all $N$ bitfield mask/shift updates
  (`applyPackedWritesInRegister`) + **1 `SSTORE s`**, costing $200$ warm gas.

Using the Three-Layer Specification Architecture:
- **Layer I (Universal Coalescing Meta-Spec & Algebraic Theorems)**:
  - `execCoalescedPackedWrites_eq_uncoalesced`: exact state equivalence for every write
    list `writes : List PackedFieldWrite` (including overlapping or overwriting writes),
  - `coalescedPackedWrites_mem_read_of_pairwiseDisjoint` &
    `coalescedSlot0_final_read_each_field`: under `PairwiseDisjointLenses`, reading each
    packed field $i$ after the single coalesced `SSTORE` returns `vᵢ % 2 ^ widthᵢ`,
  - `slotCoalescingVerifiedShim`: `VerifiedCompilerShim` instance certifying the pass,
  - `slotCoalescing_gas_saved`: strict gas savings of $(N - 1) \times 200$ gas for all
    $N \ge 2$ (saving $600$ gas per `Slot0` 4-field update).
- **Layer II (1-3 Line Projection Corollaries)**:
  Direct observational equivalence, frame preservation (`fmp` and other slots), and
  overwrite-fusion corollaries.
- **Layer III (`by decide`, `0 native_decide` Executable Witness Suite)**:
  Kernel-checked concrete witness suite for Uniswap v3/v4 `Slot0` coalescing,
  same-field overwrite fusion, and gas accounting.
-/

/-! ## Layer I.1: Packed Field Writes, Storage Slot State & Execution Semantics -/

/-- A single sub-word packed bitfield write `(lens, val)` targeting a shared 256-bit slot. -/
structure PackedFieldWrite where
  /-- Bitfield lens focusing on `[offset, offset + width)` within the 256-bit slot word. -/
  lens : PackedWordLens
  /-- Value written into the bitfield slice (automatically masked to `width` bits). -/
  val : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Abstract EVM state focused on a target packed storage slot `slotWord`,
coupled with the free-memory pointer `fmp` (`0x40`) and the root of all other
storage slots `otherSlotsRoot` (`s' ≠ s`). -/
structure SlotStorageState where
  /-- Current 256-bit word stored at the target packed storage slot `s`. -/
  slotWord : Nat := 0
  /-- Free-memory pointer at `memory[0x40]` (untouched by storage coalescing). -/
  fmp : Nat := 128
  /-- Commitment root of all storage slots other than `s` (frame-preserved). -/
  otherSlotsRoot : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Perform a single `SLOAD` on the target storage slot. -/
@[simp]
def sloadSlot (st : SlotStorageState) : Nat :=
  st.slotWord

/-- Perform a single `SSTORE` updating the target storage slot to `newWord` while
preserving `fmp` and `otherSlotsRoot`. -/
@[simp]
def sstoreSlot (st : SlotStorageState) (newWord : Nat) : SlotStorageState :=
  { st with slotWord := newWord }

/-- Execute a single uncoalesced packed field write: `SLOAD` + `lens.set` + `SSTORE`. -/
@[simp]
def execSingleUncoalescedWrite (st : SlotStorageState) (wr : PackedFieldWrite) :
    SlotStorageState :=
  sstoreSlot st (wr.lens.set (sloadSlot st) wr.val)

/-- **Uncoalesced Execution (`execUncoalescedPackedWrites`)**:
Executes $N$ sub-word packed writes as $N$ separate `SLOAD` + `setBits` + `SSTORE`
transactions on the target slot. -/
def execUncoalescedPackedWrites (st : SlotStorageState) :
    List PackedFieldWrite → SlotStorageState
  | [] => st
  | wr :: rest => execUncoalescedPackedWrites (execSingleUncoalescedWrite st wr) rest

/-- Compose a sequence of sub-word bitfield updates purely in a stack/Yul register word
without intermediate `SLOAD` or `SSTORE` operations. -/
def applyPackedWritesInRegister (word : Nat) : List PackedFieldWrite → Nat
  | [] => word
  | wr :: rest => applyPackedWritesInRegister (wr.lens.set word wr.val) rest

/-- **Coalesced Execution (`execCoalescedPackedWrites`)**:
Performs **1 `SLOAD`**, composes all $N$ bitfield masks in register via
`applyPackedWritesInRegister`, and commits the result with **1 `SSTORE`**. -/
def execCoalescedPackedWrites (st : SlotStorageState)
    (writes : List PackedFieldWrite) : SlotStorageState :=
  sstoreSlot st (applyPackedWritesInRegister (sloadSlot st) writes)

/-- In-register composition distributes over list append. -/
@[simp]
theorem applyPackedWritesInRegister_append
    (word : Nat) (xs ys : List PackedFieldWrite) :
    applyPackedWritesInRegister word (xs ++ ys) =
      applyPackedWritesInRegister (applyPackedWritesInRegister word xs) ys := by
  induction xs generalizing word with
  | nil => rfl
  | cons wr rest ih => exact ih (wr.lens.set word wr.val)

/-- **Theorem 1 (`execCoalescedPackedWrites_eq_uncoalesced`)**:
Coalescing any sequence of $N$ sub-word packed writes into a single `SLOAD` +
in-register bitwise composition + single `SSTORE` produces the exact same post-state
as $N$ uncoalesced `SLOAD`/`SSTORE` pairs. -/
@[simp]
theorem execCoalescedPackedWrites_eq_uncoalesced
    (st : SlotStorageState) (writes : List PackedFieldWrite) :
    execCoalescedPackedWrites st writes = execUncoalescedPackedWrites st writes := by
  induction writes generalizing st with
  | nil => rfl
  | cons wr rest ih =>
    unfold execUncoalescedPackedWrites execCoalescedPackedWrites applyPackedWritesInRegister
    rw [← ih (execSingleUncoalescedWrite st wr)]
    rfl

/-! ## Layer I.2: Pairwise Disjoint Lenses & Final Field Read Correctness -/

/-- Every write in `writes` focuses on a slice disjoint from `targetLens`. -/
def AllDisjointFrom (targetLens : PackedWordLens) (writes : List PackedFieldWrite) : Prop :=
  ∀ w ∈ writes, BitfieldSlice.Disjoint w.lens.slice targetLens.slice

/-- The bitfield lenses in `writes` are pairwise non-overlapping (`List.Pairwise`). -/
def PairwiseDisjointLenses (writes : List PackedFieldWrite) : Prop :=
  writes.Pairwise (fun a b => BitfieldSlice.Disjoint a.lens.slice b.lens.slice)

/-- Executable boolean checker for `PairwiseDisjointLenses`. -/
def pairwiseDisjointLensesBool : List PackedFieldWrite → Bool
  | [] => true
  | w :: rest =>
      rest.all (fun u => BitfieldSlice.disjointBool w.lens.slice u.lens.slice) &&
        pairwiseDisjointLensesBool rest

/-- Soundness of the executable `pairwiseDisjointLensesBool` checker. -/
theorem pairwiseDisjointLenses_of_bool_eq_true
    {writes : List PackedFieldWrite}
    (h : pairwiseDisjointLensesBool writes = true) :
    PairwiseDisjointLenses writes := by
  induction writes with
  | nil => exact List.Pairwise.nil
  | cons w rest ih =>
    simp only [pairwiseDisjointLensesBool, Bool.and_eq_true, List.all_eq_true,
      BitfieldSlice.disjointBool_eq_true_iff] at h
    exact List.Pairwise.cons h.1 (ih h.2)

/-- Applying in-register writes that are all disjoint from `targetLens` preserves
`targetLens.get word`. -/
theorem get_applyPackedWritesInRegister_of_allDisjoint
    (targetLens : PackedWordLens) (word : Nat) (writes : List PackedFieldWrite)
    (hdisj : AllDisjointFrom targetLens writes) :
    targetLens.get (applyPackedWritesInRegister word writes) = targetLens.get word := by
  induction writes generalizing word with
  | nil => rfl
  | cons wr rest ih =>
    unfold applyPackedWritesInRegister
    have hhead : BitfieldSlice.Disjoint wr.lens.slice targetLens.slice :=
      hdisj wr List.mem_cons_self
    have htail : AllDisjointFrom targetLens rest :=
      fun u hu => hdisj u (List.mem_cons_of_mem wr hu)
    rw [ih (wr.lens.set word wr.val) htail,
      PackedWordLens.get_set_disjoint wr.lens targetLens hhead word wr.val]

/-- **Universal Disjoint Read-After-Coalesce Theorem
(`coalescedPackedWrites_mem_read_of_pairwiseDisjoint`)**:
Whenever `writes` has pairwise disjoint lenses (`PairwiseDisjointLenses writes`),
reading any field `wr ∈ writes` after the single coalesced `SSTORE` returns
`wr.val % 2 ^ wr.lens.slice.width`. -/
theorem coalescedPackedWrites_mem_read_of_pairwiseDisjoint
    (st : SlotStorageState) (writes : List PackedFieldWrite) (wr : PackedFieldWrite)
    (hpair : PairwiseDisjointLenses writes) (hmem : wr ∈ writes) :
    wr.lens.get (execCoalescedPackedWrites st writes).slotWord =
      wr.val % 2 ^ wr.lens.slice.width := by
  induction writes generalizing st with
  | nil => cases hmem
  | cons hd tl ih =>
    rw [PairwiseDisjointLenses, List.pairwise_cons] at hpair
    rcases List.mem_cons.mp hmem with rfl | hmem_tl
    · have hall : AllDisjointFrom wr.lens tl :=
        fun u hu => (hpair.1 u hu).symm
      unfold execCoalescedPackedWrites applyPackedWritesInRegister
      simp only [sstoreSlot, sloadSlot]
      rw [get_applyPackedWritesInRegister_of_allDisjoint wr.lens _ tl hall,
        PackedWordLens.get_set_same]
    · exact ih (execSingleUncoalescedWrite st hd) hpair.2 hmem_tl

/-! ## Layer I.3: Canonical Uniswap v3/v4 `Slot0` Layout & 4-Field Coalescing -/

/-- Uniswap v3/v4 `Slot0.sqrtPriceX96` lens: bits `[0, 160)` (`uint160`). -/
def slot0SqrtPriceX96Lens : PackedWordLens :=
  ⟨{ offset := 0, width := 160 }⟩

/-- Uniswap v3/v4 `Slot0.tick` lens: bits `[160, 184)` (`int24` two's-complement word). -/
def slot0TickLens : PackedWordLens :=
  ⟨{ offset := 160, width := 24 }⟩

/-- Uniswap v3/v4 `Slot0.protocolFee` lens: bits `[184, 208)` (`uint24`). -/
def slot0ProtocolFeeLens : PackedWordLens :=
  ⟨{ offset := 184, width := 24 }⟩

/-- Uniswap v3/v4 `Slot0.lpFee` lens: bits `[208, 232)` (`uint24`). -/
def slot0LpFeeLens : PackedWordLens :=
  ⟨{ offset := 208, width := 24 }⟩

/-- Construct the 4-field packed write sequence updating Uniswap v3/v4 `Slot0`
(`sqrtPriceX96`, `tick`, `protocolFee`, `lpFee`) on the shared storage slot `0`. -/
def mkSlot0PackedWrites (sqrtPriceX96 tick protocolFee lpFee : Nat) :
    List PackedFieldWrite :=
  [ { lens := slot0SqrtPriceX96Lens, val := sqrtPriceX96 }
  , { lens := slot0TickLens, val := tick }
  , { lens := slot0ProtocolFeeLens, val := protocolFee }
  , { lens := slot0LpFeeLens, val := lpFee } ]

/-- All four `Slot0` bitfield lenses are pairwise disjoint for any field values. -/
theorem slot0_pairwiseDisjointLenses (sqrtPriceX96 tick protocolFee lpFee : Nat) :
    PairwiseDisjointLenses (mkSlot0PackedWrites sqrtPriceX96 tick protocolFee lpFee) :=
  pairwiseDisjointLenses_of_bool_eq_true rfl

/-- **Theorem 2 (`coalescedSlot0_final_read_each_field`)**:
After executing the coalesced single-`SLOAD`/single-`SSTORE` update of `Slot0`
(or any 4 pairwise-disjoint `Slot0` writes), reading each of the four sub-word
fields returns its exact truncated written value `vᵢ % 2 ^ widthᵢ`. -/
theorem coalescedSlot0_final_read_each_field
    (st : SlotStorageState) (sqrtPriceX96 tick protocolFee lpFee : Nat) :
    let writes := mkSlot0PackedWrites sqrtPriceX96 tick protocolFee lpFee
    let finalWord := (execCoalescedPackedWrites st writes).slotWord
    PairwiseDisjointLenses writes ∧
      slot0SqrtPriceX96Lens.get finalWord = sqrtPriceX96 % 2 ^ 160 ∧
      slot0TickLens.get finalWord = tick % 2 ^ 24 ∧
      slot0ProtocolFeeLens.get finalWord = protocolFee % 2 ^ 24 ∧
      slot0LpFeeLens.get finalWord = lpFee % 2 ^ 24 := by
  intro writes finalWord
  have hpair := slot0_pairwiseDisjointLenses sqrtPriceX96 tick protocolFee lpFee
  refine ⟨hpair, ?_, ?_, ?_, ?_⟩
  · exact coalescedPackedWrites_mem_read_of_pairwiseDisjoint st writes
      ⟨slot0SqrtPriceX96Lens, sqrtPriceX96⟩ hpair (by simp [writes, mkSlot0PackedWrites])
  · exact coalescedPackedWrites_mem_read_of_pairwiseDisjoint st writes
      ⟨slot0TickLens, tick⟩ hpair (by simp [writes, mkSlot0PackedWrites])
  · exact coalescedPackedWrites_mem_read_of_pairwiseDisjoint st writes
      ⟨slot0ProtocolFeeLens, protocolFee⟩ hpair (by simp [writes, mkSlot0PackedWrites])
  · exact coalescedPackedWrites_mem_read_of_pairwiseDisjoint st writes
      ⟨slot0LpFeeLens, lpFee⟩ hpair (by simp [writes, mkSlot0PackedWrites])

/-! ## Layer I.4: `VerifiedCompilerShim` Instance & Warm `SLOAD`/`SSTORE` Gas Savings -/

/-- Frame invariant for packed-slot coalescing: preserves `fmp` (`0x40`) and all
other storage slots `otherSlotsRoot`. -/
def slotCoalescingFrame (st post : SlotStorageState) : Prop :=
  post.fmp = st.fmp ∧ post.otherSlotsRoot = st.otherSlotsRoot

/-- Universal frame soundness for `execCoalescedPackedWrites`. -/
theorem execCoalescedPackedWrites_frame_sound
    (writes : List PackedFieldWrite) (st : SlotStorageState) :
    slotCoalescingFrame st (execCoalescedPackedWrites st writes) :=
  ⟨rfl, rfl⟩

/-- **Theorem 3 (`slotCoalescingVerifiedShim`)**:
`VerifiedCompilerShim` instance certifying that the single-`SLOAD`/single-`SSTORE`
packed-slot coalescing pass refines uncoalesced sequential `SLOAD`/`SSTORE` writes
and preserves the memory and storage frame. -/
def slotCoalescingVerifiedShim :
    VerifiedCompilerShim (List PackedFieldWrite) SlotStorageState SlotStorageState where
  name := "slotCoalescing"
  denoteSpec := fun writes st => execUncoalescedPackedWrites st writes
  shimImpl := fun writes st => execCoalescedPackedWrites st writes
  effects := { readsStorage := true, writesStorage := true }
  freeMemoryFrame := slotCoalescingFrame
  refines_denote := fun writes st => execCoalescedPackedWrites_eq_uncoalesced st writes
  frame_sound := execCoalescedPackedWrites_frame_sound
  non_vacuous := ⟨mkSlot0PackedWrites 1000 20 3 30, trivial⟩

/-- EIP-2929 warm `SLOAD` gas cost (`100` gas). -/
def warmSloadGas : Nat := 100

/-- EIP-2929 warm dirty `SSTORE` gas cost (`100` gas). -/
def warmSstoreGas : Nat := 100

/-- Combined gas cost of one warm `SLOAD` + `SSTORE` read-modify-write pair (`200` gas). -/
def warmSlotAccessPairGas : Nat := warmSloadGas + warmSstoreGas

/-- Total `SLOAD` + `SSTORE` gas consumed by $N$ uncoalesced packed writes ($N \times 200$). -/
def uncoalescedPackedWritesGas (numWrites : Nat) : Nat :=
  numWrites * warmSlotAccessPairGas

/-- Total `SLOAD` + `SSTORE` gas consumed by coalesced packed writes ($0$ when $N = 0$,
$200$ when $N \ge 1$). -/
def coalescedPackedWritesGas (numWrites : Nat) : Nat :=
  if numWrites == 0 then 0 else warmSlotAccessPairGas

/-- Gas saved by coalescing $N$ sub-word writes on the same storage slot. -/
def slotCoalescingGasSaved (numWrites : Nat) : Nat :=
  uncoalescedPackedWritesGas numWrites - coalescedPackedWritesGas numWrites

/-- **Theorem 4 (`slotCoalescing_gas_saved`)**:
For every sequence of $N \ge 2$ packed writes to the same slot, slot coalescing
strictly saves $(N - 1) \times 200$ gas (eliminating $N - 1$ warm `SLOAD` + `SSTORE`
pairs). -/
theorem slotCoalescing_gas_saved (numWrites : Nat) (hge : 2 ≤ numWrites) :
    slotCoalescingGasSaved numWrites = (numWrites - 1) * 200 ∧
      0 < slotCoalescingGasSaved numWrites := by
  have hne : (numWrites == 0) = false := beq_false_of_ne (by omega)
  simp only [slotCoalescingGasSaved, uncoalescedPackedWritesGas,
    coalescedPackedWritesGas, warmSlotAccessPairGas, warmSloadGas, warmSstoreGas,
    hne, Bool.false_eq_true, ↓reduceIte]
  omega

/-! ## Layer II: 1-3 Line Projection & Fusion Corollaries -/

/-- Layer II observational refinement corollary for `slotCoalescingVerifiedShim`. -/
theorem slotCoalescing_obs_eq
    (writes : List PackedFieldWrite) (st : SlotStorageState) :
    slotCoalescingVerifiedShim.shimImpl writes st =
      slotCoalescingVerifiedShim.denoteSpec writes st :=
  slotCoalescingVerifiedShim.obs_eq writes st

/-- Layer II frame corollary for `slotCoalescingVerifiedShim`. -/
theorem slotCoalescing_denote_frame_sound
    (writes : List PackedFieldWrite) (st : SlotStorageState) :
    slotCoalescingFrame st (slotCoalescingVerifiedShim.denoteSpec writes st) :=
  slotCoalescingVerifiedShim.denote_frame_sound writes st

/-- Two consecutive writes to the same packed lens `lens` coalesce into the single
final write `(lens, v₂)` (`PackedWordLens.set_set_fuse`). -/
@[simp]
theorem execCoalescedPackedWrites_same_lens_fuse
    (st : SlotStorageState) (lens : PackedWordLens) (v₁ v₂ : Nat)
    (rest : List PackedFieldWrite) :
    execCoalescedPackedWrites st (⟨lens, v₁⟩ :: ⟨lens, v₂⟩ :: rest) =
      execCoalescedPackedWrites st (⟨lens, v₂⟩ :: rest) := by
  simp [execCoalescedPackedWrites, applyPackedWritesInRegister]

/-- Concrete gas-saving corollary for Uniswap v3/v4 `Slot0` ($N = 4$ fields):
coalescing saves $3 \times 200 = 600$ gas per `Slot0` update. -/
theorem slot0_coalescing_saves_600_gas :
    slotCoalescingGasSaved 4 = 600 ∧
      uncoalescedPackedWritesGas 4 = 800 ∧
      coalescedPackedWritesGas 4 = 200 := by
  decide

/-! ## Layer III: Kernel-Checked (`by decide`, `0 native_decide`) Executable Witness Suite -/

/-- Executable witness verifying `Slot0` 4-field coalescing equivalence, pairwise
disjointness, exact field readback, overwrite fusion, frame preservation, and
$600$-gas savings. -/
def checkSlotCoalescingWitnessSuite : Bool :=
  let st₀ : SlotStorageState :=
    { slotWord := 0xdeadbeef, fmp := 128, otherSlotsRoot := 777 }
  let writes := mkSlot0PackedWrites 0x123456789abcdef 0x000abc 0x000015 0x000bb8
  let coalesced := slotCoalescingVerifiedShim.shimImpl writes st₀
  let uncoalesced := slotCoalescingVerifiedShim.denoteSpec writes st₀
  let overwriteWrites : List PackedFieldWrite :=
    [ ⟨slot0TickLens, 111⟩, ⟨slot0TickLens, 222⟩, ⟨slot0LpFeeLens, 500⟩ ]
  let fusedWrites : List PackedFieldWrite :=
    [ ⟨slot0TickLens, 222⟩, ⟨slot0LpFeeLens, 500⟩ ]
  (coalesced == uncoalesced) &&
    pairwiseDisjointLensesBool writes &&
    (slot0SqrtPriceX96Lens.get coalesced.slotWord == 0x123456789abcdef) &&
    (slot0TickLens.get coalesced.slotWord == 0x000abc) &&
    (slot0ProtocolFeeLens.get coalesced.slotWord == 0x000015) &&
    (slot0LpFeeLens.get coalesced.slotWord == 0x000bb8) &&
    (coalesced.fmp == 128) &&
    (coalesced.otherSlotsRoot == 777) &&
    (execCoalescedPackedWrites st₀ overwriteWrites ==
      execCoalescedPackedWrites st₀ fusedWrites) &&
    (slotCoalescingGasSaved 4 == 600) &&
    (slotCoalescingGasSaved 2 == 200)

/-- Kernel-checked (`by decide`, `0 native_decide`) proof of `checkSlotCoalescingWitnessSuite`. -/
theorem checkSlotCoalescingWitnessSuite_eq_true :
    checkSlotCoalescingWitnessSuite = true := by
  decide

end Compiler.Proofs.SlotCoalescingShim
