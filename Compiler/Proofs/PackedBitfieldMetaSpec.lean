/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Verity.Core.Model.Types

namespace Compiler.Proofs.PackedBitfieldMetaSpec

open Compiler
open Compiler.CompilationModel

/-!
# Meta-Spec 10: Packed Sub-Word Bitfield & Relative Slot Offset Algebra

This module formalizes **Meta-Spec 10** in the Three-Layer Specification Architecture:

1. **Sub-Word Bitfield Lens Algebra (`PackedBitfieldMetaSpec`, `#2417`, `#1993`)**:
   - Sub-word storage scalar catalog (`SubWordScalar`: `Bool`, `Uint8`, `Uint16`,
     `Uint32`, `Uint64`, `Uint96`, `Uint128`, `Address`, `Bytes32`).
   - Exact arithmetic bitfield extraction (`extractBits word offset width`) and
     bitfield update (`updateBits word offset width val`) over `Nat` / `Uint256` words.
   - Universal algebraic lens laws:
     - `extractBits_updateBits_same` (Get-Put / Read-After-Write),
     - `extractBits_updateBits_disjoint` (Put-Get Disjoint Frame),
     - `updateBits_updateBits_same_fuse` (Put-Put / `SLOAD`-`SSTORE` Fusion).
2. **Relative Slot Offset & Stride Algebra (`RelativeSlotOffsetMetaSpec`, `#2417`, `#2420`)**:
   - `FixedArray` multi-slot stride calculation (`fixedArraySlot baseSlot idx elemStride`)
     and sub-word / multi-slot non-collision (`fixedArraySlot_subSlot_nonCollision`).
   - ERC-7201 / single- and multi-parent inheritance relative slot offset composition
     (`inheritedSlotOffset parentSlotOffset localSlot`) and parent/child range disjointness.
3. **Layer III Executable Witness Suite (`by decide`, `0 native_decide`)**:
   - Kernel-checked positive and negative boundary witnesses across all sub-word scalar types,
     packed bitfield lens laws, and relative slot offset calculations.
-/

/-! ## Sub-Word Scalar Catalog & Bitfield Slices -/

/-- Canonical Solidity storage scalar types participating in 256-bit word packing (`#2417`). -/
inductive SubWordScalar where
  | bool
  | uint8
  | uint16
  | uint32
  | uint64
  | uint96
  | uint128
  | address
  | bytes32
  deriving DecidableEq, Repr, Inhabited

namespace SubWordScalar

/-- Storage bit width of each Solidity scalar type in a packed 256-bit slot. -/
@[simp]
def bitWidth : SubWordScalar → Nat
  | .bool => 8
  | .uint8 => 8
  | .uint16 => 16
  | .uint32 => 32
  | .uint64 => 64
  | .uint96 => 96
  | .uint128 => 128
  | .address => 160
  | .bytes32 => 256

/-- Every `SubWordScalar` has a positive bit width bounded by 256 bits. -/
theorem bitWidth_pos_and_le_256 (s : SubWordScalar) :
    0 < s.bitWidth ∧ s.bitWidth ≤ 256 := by
  cases s <;> decide

end SubWordScalar

/-- A bitfield slice `[offset, offset + width)` within a 256-bit EVM storage word. -/
structure BitfieldSlice where
  /-- Least-significant bit offset within the storage word. -/
  offset : Nat
  /-- Bit width of the packed slice. -/
  width : Nat
  deriving DecidableEq, Repr, Inhabited

namespace BitfieldSlice

/-- Convert a `CompilationModel.PackedBits` descriptor into a `BitfieldSlice`. -/
@[simp]
def ofPackedBits (pb : PackedBits) : BitfieldSlice :=
  { offset := pb.offset, width := pb.width }

/-- Convert a `BitfieldSlice` into a `CompilationModel.PackedBits` descriptor. -/
@[simp]
def toPackedBits (s : BitfieldSlice) : PackedBits :=
  { offset := s.offset, width := s.width }

/-- Construct a `BitfieldSlice` for a `SubWordScalar` at bit `offset`. -/
@[simp]
def ofScalar (offset : Nat) (scalar : SubWordScalar) : BitfieldSlice :=
  { offset := offset, width := scalar.bitWidth }

/-- Exclusive upper bit bound `offset + width`. -/
@[simp]
def endBit (s : BitfieldSlice) : Nat :=
  s.offset + s.width

/-- A slice is well-formed within a 256-bit EVM word when `offset + width ≤ 256`. -/
def WellFormed (s : BitfieldSlice) : Prop :=
  s.offset + s.width ≤ 256

/-- Executable boolean check for `WellFormed`. -/
def isWellFormed (s : BitfieldSlice) : Bool :=
  decide (s.offset + s.width ≤ 256)

/-- Two bitfield slices are non-overlapping when one ends at or before the other starts. -/
def Disjoint (a b : BitfieldSlice) : Prop :=
  a.offset + a.width ≤ b.offset ∨ b.offset + b.width ≤ a.offset

/-- Executable boolean check for `Disjoint`. -/
def disjointBool (a b : BitfieldSlice) : Bool :=
  decide (a.offset + a.width ≤ b.offset ∨ b.offset + b.width ≤ a.offset)

@[simp]
theorem disjointBool_eq_true_iff (a b : BitfieldSlice) :
    disjointBool a b = true ↔ Disjoint a b := by
  simp [disjointBool, Disjoint]

theorem Disjoint.symm {a b : BitfieldSlice} (h : Disjoint a b) : Disjoint b a := by
  rcases h with h1 | h2
  · exact Or.inr h1
  · exact Or.inl h2

end BitfieldSlice

/-! ## Sub-Word Bitfield Extraction & Update Operations -/

/-- Extract the `width`-bit field at bit `offset` from `word` (`(word >> offset) & ((1 << width) - 1)`). -/
def extractBits (word offset width : Nat) : Nat :=
  (word / 2 ^ offset) % 2 ^ width

/-- Clear the `[offset, offset + width)` bit range of `word`, preserving low bits `< offset`
and high bits `≥ offset + width`. -/
def clearBits (word offset width : Nat) : Nat :=
  (word % 2 ^ offset) + (word / 2 ^ (offset + width)) * 2 ^ (offset + width)

/-- Update the `[offset, offset + width)` bitfield of `word` with `val % 2 ^ width`. -/
def updateBits (word offset width val : Nat) : Nat :=
  (word % 2 ^ offset) +
    ((val % 2 ^ width) + (word / 2 ^ (offset + width)) * 2 ^ width) * 2 ^ offset

/-- Extracted bitfields are always strictly bounded by `2 ^ width`. -/
theorem extractBits_lt_two_pow (word offset width : Nat) :
    extractBits word offset width < 2 ^ width :=
  Nat.mod_lt _ (Nat.two_pow_pos width)

/-- Dividing `updateBits word offset width val` by `2 ^ offset` isolates the updated
field plus the preserved upper word fragment. -/
@[simp]
theorem div_two_pow_updateBits (word offset width val : Nat) :
    updateBits word offset width val / 2 ^ offset =
      (val % 2 ^ width) + (word / 2 ^ (offset + width)) * 2 ^ width := by
  unfold updateBits
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos offset),
    Nat.div_eq_of_lt (Nat.mod_lt word (Nat.two_pow_pos offset)), Nat.zero_add]

/-- Modulo `2 ^ offset`, `updateBits word offset width val` preserves the low bits of `word`. -/
@[simp]
theorem mod_two_pow_updateBits (word offset width val : Nat) :
    updateBits word offset width val % 2 ^ offset = word % 2 ^ offset := by
  unfold updateBits
  rw [Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- Dividing `updateBits word offset width val` by `2 ^ (offset + width)` preserves the
high bits of `word` above `offset + width`. -/
@[simp]
theorem div_two_pow_add_updateBits (word offset width val : Nat) :
    updateBits word offset width val / 2 ^ (offset + width) =
      word / 2 ^ (offset + width) := by
  have hdiv : ∀ x, x / 2 ^ (offset + width) = (x / 2 ^ offset) / 2 ^ width := by
    intro x
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [hdiv (updateBits word offset width val), div_two_pow_updateBits,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos width),
    Nat.div_eq_of_lt (Nat.mod_lt val (Nat.two_pow_pos width)), Nat.zero_add]

/-! ## Layer I: Algebraic Bitfield Lens Laws & `PackedBitfieldMetaSpec` -/

/-- **Lens Law 1 (`extractBits_updateBits_same`)**:
Reading back a bitfield immediately after updating it yields `val % 2 ^ width`. -/
@[simp]
theorem extractBits_updateBits_same (word offset width val : Nat) :
    extractBits (updateBits word offset width val) offset width = val % 2 ^ width := by
  unfold extractBits
  rw [div_two_pow_updateBits, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- Explicit unfolding equation for a single `updateBits` application. -/
theorem updateBits_eq (word offset width val : Nat) :
    updateBits word offset width val =
      (word % 2 ^ offset) +
        ((val % 2 ^ width) + (word / 2 ^ (offset + width)) * 2 ^ width) * 2 ^ offset :=
  rfl

/-- **Lens Law 3 (`updateBits_updateBits_same_fuse`)**:
Two sequential updates to the same bitfield `(offset, width)` fuse into a single update
with the second value (`#2417`, `#1993`), eliminating redundant `SLOAD`/`SSTORE` pairs. -/
@[simp]
theorem updateBits_updateBits_same_fuse (word offset width v₁ v₂ : Nat) :
    updateBits (updateBits word offset width v₁) offset width v₂ =
      updateBits word offset width v₂ := by
  rw [updateBits_eq (updateBits word offset width v₁),
    mod_two_pow_updateBits, div_two_pow_add_updateBits, ← updateBits_eq]

/-- Helper: `updateBits` preserves division by `2 ^ oB` whenever `oA + wA ≤ oB`. -/
theorem div_two_pow_updateBits_of_le
    (word oA wA val oB : Nat) (hle : oA + wA ≤ oB) :
    updateBits word oA wA val / 2 ^ oB = word / 2 ^ oB := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiv : ∀ x, x / 2 ^ (oA + wA + d) = (x / 2 ^ (oA + wA)) / 2 ^ d := by
    intro x
    rw [Nat.pow_add, Nat.div_div_eq_div_mul]
  rw [hdiv (updateBits word oA wA val), hdiv word, div_two_pow_add_updateBits]

/-- Helper: adding a multiple of `2 ^ (o + k + d)` does not change `extractBits · o k`. -/
theorem extractBits_add_mul_two_pow_add
    (r q o k d : Nat) :
    extractBits (r + q * 2 ^ (o + k + d)) o k = extractBits r o k := by
  unfold extractBits
  rw [Nat.add_assoc o k d, Nat.pow_add 2 o (k + d), Nat.pow_add 2 k d,
    Nat.mul_comm (2 ^ o) (2 ^ k * 2 ^ d), ← Nat.mul_assoc,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos o),
    Nat.mul_comm (2 ^ k) (2 ^ d), ← Nat.mul_assoc q (2 ^ d) (2 ^ k),
    Nat.add_mul_mod_self_right]

/-- Helper: `extractBits` depends only on `word % 2 ^ m` whenever `o + k ≤ m`. -/
theorem extractBits_mod_two_pow
    (word o k m : Nat) (hle : o + k ≤ m) :
    extractBits (word % 2 ^ m) o k = extractBits word o k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdecomp := (Nat.mod_add_div word (2 ^ (o + k + d))).symm
  rw [Nat.mul_comm (2 ^ (o + k + d)) (word / 2 ^ (o + k + d))] at hdecomp
  have h := extractBits_add_mul_two_pow_add
    (word % 2 ^ (o + k + d)) (word / 2 ^ (o + k + d)) o k d
  rw [← hdecomp] at h
  exact h.symm

/-- **Lens Law 2 (`extractBits_updateBits_disjoint`)**:
Updating field `A = (offsetA, widthA)` preserves any non-overlapping field
`B = (offsetB, widthB)` satisfying `offsetA + widthA ≤ offsetB ∨ offsetB + widthB ≤ offsetA`. -/
theorem extractBits_updateBits_disjoint
    (word offsetA widthA val offsetB widthB : Nat)
    (hdisj : offsetA + widthA ≤ offsetB ∨ offsetB + widthB ≤ offsetA) :
    extractBits (updateBits word offsetA widthA val) offsetB widthB =
      extractBits word offsetB widthB := by
  rcases hdisj with hle | hle
  · unfold extractBits
    rw [div_two_pow_updateBits_of_le word offsetA widthA val offsetB hle]
  · rw [← extractBits_mod_two_pow (updateBits word offsetA widthA val) offsetB widthB offsetA hle,
      mod_two_pow_updateBits, extractBits_mod_two_pow word offsetB widthB offsetA hle]

/-- **Layer I Universal Meta-Specification (`PackedBitfieldMetaSpec`)**:
Parametric lens specification certifying Get-Put, Put-Put (`SLOAD`/`SSTORE` fusion),
and Put-Get Disjoint Frame laws for any pair of bitfield slices `a` and `b`. -/
structure PackedBitfieldMetaSpec (a b : BitfieldSlice) : Prop where
  /-- Reading slice `a` after updating `a` returns the truncated written value. -/
  get_put_same :
    ∀ word val,
      extractBits (updateBits word a.offset a.width val) a.offset a.width =
        val % 2 ^ a.width
  /-- Two back-to-back updates to slice `a` fuse into a single update (`#1993`). -/
  put_put_fuse :
    ∀ word v₁ v₂,
      updateBits (updateBits word a.offset a.width v₁) a.offset a.width v₂ =
        updateBits word a.offset a.width v₂
  /-- Updating slice `a` preserves slice `b` whenever `a` and `b` are disjoint (`#2417`). -/
  get_put_disjoint :
    BitfieldSlice.Disjoint a b →
      ∀ word val,
        extractBits (updateBits word a.offset a.width val) b.offset b.width =
          extractBits word b.offset b.width

/-- **Universal Theorem (`packedBitfield_satisfies_metaSpec`)**:
Every pair of bitfield slices `a, b : BitfieldSlice` satisfies `PackedBitfieldMetaSpec a b`. -/
theorem packedBitfield_satisfies_metaSpec (a b : BitfieldSlice) :
    PackedBitfieldMetaSpec a b where
  get_put_same word val := extractBits_updateBits_same word a.offset a.width val
  put_put_fuse word v₁ v₂ := updateBits_updateBits_same_fuse word a.offset a.width v₁ v₂
  get_put_disjoint hdisj word val :=
    extractBits_updateBits_disjoint word a.offset a.width val b.offset b.width hdisj

/-! ## Layer II: `PackedWordLens` & Projection Corollaries -/

/-- First-class read/write lens focusing on a `BitfieldSlice` inside a 256-bit word. -/
structure PackedWordLens where
  /-- Underlying bitfield slice `[offset, offset + width)`. -/
  slice : BitfieldSlice
  deriving DecidableEq, Repr, Inhabited

namespace PackedWordLens

/-- Read the focused bitfield slice from `word`. -/
@[simp]
def get (lens : PackedWordLens) (word : Nat) : Nat :=
  extractBits word lens.slice.offset lens.slice.width

/-- Write `val` into the focused bitfield slice of `word`. -/
@[simp]
def set (lens : PackedWordLens) (word val : Nat) : Nat :=
  updateBits word lens.slice.offset lens.slice.width val

/-- Layer II Get-Put corollary for `PackedWordLens`. -/
@[simp]
theorem get_set_same (lens : PackedWordLens) (word val : Nat) :
    lens.get (lens.set word val) = val % 2 ^ lens.slice.width :=
  (packedBitfield_satisfies_metaSpec lens.slice lens.slice).get_put_same word val

/-- Layer II Get-Put corollary when `val < 2 ^ lens.slice.width`. -/
theorem get_set_same_of_lt (lens : PackedWordLens) (word val : Nat)
    (hval : val < 2 ^ lens.slice.width) :
    lens.get (lens.set word val) = val := by
  rw [get_set_same, Nat.mod_eq_of_lt hval]

/-- Layer II Put-Put fusion corollary for `PackedWordLens` (`#1993`). -/
@[simp]
theorem set_set_fuse (lens : PackedWordLens) (word v₁ v₂ : Nat) :
    lens.set (lens.set word v₁) v₂ = lens.set word v₂ :=
  (packedBitfield_satisfies_metaSpec lens.slice lens.slice).put_put_fuse word v₁ v₂

/-- Layer II Put-Get disjoint frame corollary for two `PackedWordLens` focuses (`#2417`). -/
theorem get_set_disjoint (lensA lensB : PackedWordLens)
    (hdisj : BitfieldSlice.Disjoint lensA.slice lensB.slice)
    (word val : Nat) :
    lensB.get (lensA.set word val) = lensB.get word :=
  (packedBitfield_satisfies_metaSpec lensA.slice lensB.slice).get_put_disjoint hdisj word val

end PackedWordLens

/-! ## Relative Slot Offset & `FixedArray` Stride Meta-Specification (`#2417`, `#2420`) -/

/-- Compute the storage slot of element `idx` in a `FixedArray` with multi-slot
stride `elemStride` anchored at `baseSlot`. -/
@[simp]
def fixedArraySlot (baseSlot idx elemStride : Nat) : Nat :=
  baseSlot + idx * elemStride

/-- Compute the storage slot of word `subSlot` (`subSlot < elemStride`) inside
element `idx` of a multi-slot `FixedArray`. -/
@[simp]
def fixedArraySubSlot (baseSlot idx elemStride subSlot : Nat) : Nat :=
  baseSlot + idx * elemStride + subSlot

/-- Compute the effective storage slot under ERC-7201 / inheritance relative slot
offsetting (`parentSlotOffset + localSlot`). -/
@[simp]
def inheritedSlotOffset (parentSlotOffset localSlot : Nat) : Nat :=
  parentSlotOffset + localSlot

/-- Injectivity of `fixedArraySlot` for positive element stride `0 < elemStride`. -/
theorem fixedArraySlot_injective
    {baseSlot i j elemStride : Nat}
    (hstride : 0 < elemStride)
    (heq : fixedArraySlot baseSlot i elemStride = fixedArraySlot baseSlot j elemStride) :
    i = j := by
  simp only [fixedArraySlot] at heq
  have hmul : i * elemStride = j * elemStride := Nat.add_left_cancel heq
  exact Nat.eq_of_mul_eq_mul_right hstride hmul

/-- Non-collision of multi-slot `FixedArray` element sub-words (`#2417`):
if `r₁ < elemStride` and `r₂ < elemStride`, equal resolved slots imply `i = j ∧ r₁ = r₂`. -/
theorem fixedArraySubSlot_nonCollision
    {baseSlot i j elemStride r₁ r₂ : Nat}
    (hr₁ : r₁ < elemStride) (hr₂ : r₂ < elemStride)
    (heq : fixedArraySubSlot baseSlot i elemStride r₁ =
      fixedArraySubSlot baseSlot j elemStride r₂) :
    i = j ∧ r₁ = r₂ := by
  simp only [fixedArraySubSlot, Nat.add_assoc] at heq
  have hlin : r₁ + i * elemStride = r₂ + j * elemStride := by omega
  have hdiv : (r₁ + i * elemStride) / elemStride = (r₂ + j * elemStride) / elemStride :=
    congrArg (· / elemStride) hlin
  have hpos : 0 < elemStride := by omega
  rw [Nat.add_mul_div_right _ _ hpos, Nat.add_mul_div_right _ _ hpos,
    Nat.div_eq_of_lt hr₁, Nat.div_eq_of_lt hr₂, Nat.zero_add, Nat.zero_add] at hdiv
  subst hdiv
  exact ⟨rfl, by omega⟩

/-- Injectivity of `inheritedSlotOffset` for any fixed `parentSlotOffset` (`#2420`). -/
theorem inheritedSlotOffset_injective
    {parentSlotOffset s₁ s₂ : Nat}
    (heq : inheritedSlotOffset parentSlotOffset s₁ = inheritedSlotOffset parentSlotOffset s₂) :
    s₁ = s₂ :=
  Nat.add_left_cancel heq

/-- Disjointness between ancestor slots (`< parentSpan`) and child slots offset by
`parentSlotOffset + parentSpan` (`#2420`). -/
theorem inheritedSlotOffset_parent_child_disjoint
    {parentSlotOffset parentSpan parentLocal childLocal : Nat}
    (hparent : parentLocal < parentSpan) :
    inheritedSlotOffset parentSlotOffset parentLocal ≠
      inheritedSlotOffset (parentSlotOffset + parentSpan) childLocal := by
  simp only [inheritedSlotOffset]
  omega

/-- **Layer I Meta-Specification (`RelativeSlotOffsetMetaSpec`)**:
Certifies injectivity and non-collision for multi-slot `FixedArray` strides and
inherited / ERC-7201 relative storage slot offsets (`#2417`, `#2420`). -/
structure RelativeSlotOffsetMetaSpec
    (parentSlotOffset parentSpan baseSlot elemStride : Nat) : Prop where
  /-- Distinct array indices map to distinct base slots. -/
  array_stride_injective :
    ∀ i j,
      fixedArraySlot baseSlot i elemStride = fixedArraySlot baseSlot j elemStride →
        i = j
  /-- Distinct `(index, subSlot)` pairs with `subSlot < elemStride` never collide. -/
  array_subSlot_nonCollision :
    ∀ i j r₁ r₂,
      r₁ < elemStride → r₂ < elemStride →
      fixedArraySubSlot baseSlot i elemStride r₁ =
        fixedArraySubSlot baseSlot j elemStride r₂ →
        i = j ∧ r₁ = r₂
  /-- Relative slot offsetting is injective on local slot numbers. -/
  inherited_offset_injective :
    ∀ s₁ s₂,
      inheritedSlotOffset parentSlotOffset s₁ =
        inheritedSlotOffset parentSlotOffset s₂ →
        s₁ = s₂
  /-- Ancestor slots bounded by `parentSpan` never collide with child slots shifted by `parentSpan`. -/
  parent_child_disjoint :
    ∀ parentLocal childLocal,
      parentLocal < parentSpan →
        inheritedSlotOffset parentSlotOffset parentLocal ≠
          inheritedSlotOffset (parentSlotOffset + parentSpan) childLocal

/-- **Universal Theorem (`relativeSlotOffset_satisfies_metaSpec`)**:
For every `parentSlotOffset`, `parentSpan`, `baseSlot`, and positive `elemStride > 0`,
`RelativeSlotOffsetMetaSpec` holds universally. -/
theorem relativeSlotOffset_satisfies_metaSpec
    (parentSlotOffset parentSpan baseSlot elemStride : Nat)
    (hstride : 0 < elemStride) :
    RelativeSlotOffsetMetaSpec parentSlotOffset parentSpan baseSlot elemStride where
  array_stride_injective _ _ heq := fixedArraySlot_injective hstride heq
  array_subSlot_nonCollision _ _ _ _ hr₁ hr₂ heq :=
    fixedArraySubSlot_nonCollision hr₁ hr₂ heq
  inherited_offset_injective _ _ heq := inheritedSlotOffset_injective heq
  parent_child_disjoint _ _ hlt := inheritedSlotOffset_parent_child_disjoint hlt

/-! ## Layer III: Kernel-Checked Witness Suite (`by decide`, `0 native_decide`) -/

/-- Concrete packed slot layout packing `Bool` (offset 0, width 8), `Uint8` (offset 8, width 8),
`Uint16` (offset 16, width 16), `Uint32` (offset 32, width 32), `Uint64` (offset 64, width 64),
and `Uint128` (offset 128, width 128) into a single 256-bit word. -/
def samplePackedSlices : List BitfieldSlice :=
  [ BitfieldSlice.ofScalar 0 .bool
  , BitfieldSlice.ofScalar 8 .uint8
  , BitfieldSlice.ofScalar 16 .uint16
  , BitfieldSlice.ofScalar 32 .uint32
  , BitfieldSlice.ofScalar 64 .uint64
  , BitfieldSlice.ofScalar 128 .uint128 ]

/-- Positive witness: all 6 sub-word slices in `samplePackedSlices` fit within 256 bits. -/
theorem samplePackedSlices_all_wellFormed :
    samplePackedSlices.all BitfieldSlice.isWellFormed = true := by decide

/-- Positive witness: `Address` (160 bits at offset 0) and `Uint96` (96 bits at offset 160)
pack cleanly into one 256-bit storage word and are disjoint. -/
theorem address_and_uint96_pack_disjoint :
    let addrSlice := BitfieldSlice.ofScalar 0 .address
    let uint96Slice := BitfieldSlice.ofScalar 160 .uint96
    addrSlice.isWellFormed && uint96Slice.isWellFormed &&
      BitfieldSlice.disjointBool addrSlice uint96Slice = true := by decide

/-- Negative witness: overlapping slices `[0, 16)` and `[8, 24)` are rejected by `disjointBool`. -/
theorem overlapping_slices_not_disjoint :
    BitfieldSlice.disjointBool ⟨0, 16⟩ ⟨8, 16⟩ = false := by decide

/-- Negative witness: a slice whose `offset + width > 256` is rejected by `isWellFormed`. -/
theorem overflowing_slice_not_wellFormed :
    (BitfieldSlice.ofScalar 160 .uint128).isWellFormed = false := by decide

/-- Positive witness: sequential updates to packed fields `(flags: Uint16 @ 0, epoch: Uint32 @ 16)`
preserve each other and fuse redundant writes on the same slice. -/
theorem packed_lens_execution_witness :
    let flagsLens : PackedWordLens := ⟨BitfieldSlice.ofScalar 0 .uint16⟩
    let epochLens : PackedWordLens := ⟨BitfieldSlice.ofScalar 16 .uint32⟩
    let w₀ := 0
    let w₁ := flagsLens.set w₀ 7
    let w₂ := epochLens.set w₁ 9
    let w₃ := flagsLens.set (flagsLens.set w₂ 99) 42
    flagsLens.get w₂ = 7 ∧
      epochLens.get w₂ = 9 ∧
      flagsLens.get w₃ = 42 ∧
      epochLens.get w₃ = 9 ∧
      w₃ = flagsLens.set w₂ 42 := by decide

/-- Positive & negative witnesses for multi-slot `FixedArray` stride and inherited slot offsets. -/
theorem relative_slot_offset_witness :
    fixedArraySubSlot 10 0 3 2 ≠ fixedArraySubSlot 10 1 3 0 ∧
      inheritedSlotOffset 5 2 = 7 ∧
      (inheritedSlotOffset 5 2 != inheritedSlotOffset (5 + 4) 0) = true := by decide

end Compiler.Proofs.PackedBitfieldMetaSpec
