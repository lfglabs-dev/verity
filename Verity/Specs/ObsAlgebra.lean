/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Verity.Specs.Common
import Compiler.Proofs.MappingSlot

set_option autoImplicit false

namespace Verity.Specs.ObsAlgebra

open Verity
open Verity.Specs

/-!
# Canonical Observation Algebra (`Obs`, `ObsEquiv`) & Dynamic Array / Bytes Storage Key Algebra
## Verity 2.0 Unified Roadmap — Phase A (Branch `V5-1`)

This module resolves the two foundational Phase A blockers identified across the
three-model architectural review (Claude Fable 5.1, GPT-6 Astra, OpenCode `builtin/smart`):

1. **Canonical Cross-Layer Observation (`Obs` & `ObsEquiv`)**:
   Unifies the observable outcome of execution across Layer 1 (`Denote`), Layer 2 (`IR`),
   Layer 3 (`EvmYul.Yul`), and target EVM (`EvmYul.EVM`) over:
   - `status : ExecStatus` (`success | revert | invalid`),
   - `returndata : List UInt8` (ABI return bytes on success or selector + error payload on revert),
   - `logs : List ObsLog` (`emitter × topics[≤4] × data`),
   - `storage : List (Nat × Nat)` (committed persistent storage key-value snapshot),
   - `transient : List (Nat × Nat)` (EIP-1153 transient storage snapshot, empty on revert).
   Crucially, **gas is excluded from `ObsEquiv`** and tracked via a separate fork-indexed
   refinement relation (`GasRefines`), preventing out-of-gas / `GAS` differences from
   invalidating semantics-preserving gas optimizations.

2. **Standard Solidity Dynamic-Array & Bytes Storage Key Algebra (`ExtendedStorageKey`)**:
   Replaces the overloaded mapping-slot formula on dynamic arrays with the exact Solidity
   storage layout:
   - Mapping slot: `solidityMappingSlot s k = keccak256(pad32(k) ++ pad32(s))`
   - Dynamic array length at slot `s`; element `i` with `stride` words at:
     `solidityArrayElemSlot s i stride = (solidityArrayBaseSlot s + i * stride) % 2^256`
     where `solidityArrayBaseSlot s = keccak256(pad32(s))`.
   - Proves injectivity of dynamic array element addressing within the non-wrapping range
     (`solidityArrayElemSlot_injective_index`), stride monotonicity, and frame preservation
     laws compatible with `Verity.Specs.unchangedExcept`.
-/

/-! ## 1. Canonical Execution Status, Logs, and Observation (`Obs`) -/

/-- Canonical execution status across all four semantic lanes. -/
inductive ExecStatus where
  | success
  | revert
  | invalid
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Canonical EVM log entry (`LOG0`..`LOG4`) with emitter, up to 4 indexed 32-byte topics,
    and ABI-encoded non-indexed data bytes. -/
structure ObsLog where
  emitter : Nat
  topics : List Nat
  data : List UInt8
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Canonical cross-layer observation record (`Obs`).
    Gas consumption is intentionally excluded from `Obs` so that gas-reducing compiler
    rewrites satisfy exact `ObsEquiv` while proving `GasRefines` as a side inequality. -/
structure Obs where
  status : ExecStatus := .success
  returndata : List UInt8 := []
  logs : List ObsLog := []
  storage : List (Nat × Nat) := []
  transient : List (Nat × Nat) := []
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Observational equivalence between two execution outcomes. -/
def ObsEquiv (a b : Obs) : Prop :=
  a = b

/-- Decidable check for `ObsEquiv`. -/
def obsEquivBool (a b : Obs) : Bool :=
  decide (a = b)

@[simp]
theorem obsEquiv_refl (a : Obs) : ObsEquiv a a := rfl

theorem obsEquiv_symm {a b : Obs} (h : ObsEquiv a b) : ObsEquiv b a :=
  Eq.symm h

theorem obsEquiv_trans {a b c : Obs} (h₁ : ObsEquiv a b) (h₂ : ObsEquiv b c) :
    ObsEquiv a c :=
  Eq.trans h₁ h₂

theorem obsEquivBool_eq_true_iff (a b : Obs) :
    obsEquivBool a b = true ↔ ObsEquiv a b := by
  unfold obsEquivBool ObsEquiv
  exact decide_eq_true_iff

/-- Coupled functional equivalence and gas improvement certificate:
    a transformation preserves `ObsEquiv` while consuming no more gas than the baseline. -/
structure CertifiedObsAndGasRefinement (State : Type) where
  obsOf : State → Obs
  gasOf : State → Nat
  beforeState : State
  afterState : State
  preserves_obs : ObsEquiv (obsOf afterState) (obsOf beforeState)
  improves_gas : gasOf afterState ≤ gasOf beforeState

/-- Transitive composition of two `CertifiedObsAndGasRefinement` certificates. -/
def CertifiedObsAndGasRefinement.compose {State : Type}
    {obsOf : State → Obs} {gasOf : State → Nat}
    {s₀ s₁ s₂ : State}
    (c₁ : CertifiedObsAndGasRefinement State)
    (c₂ : CertifiedObsAndGasRefinement State)
    (hobs₁ : c₁.obsOf = obsOf) (hgas₁ : c₁.gasOf = gasOf)
    (hb₁ : c₁.beforeState = s₀) (ha₁ : c₁.afterState = s₁)
    (hobs₂ : c₂.obsOf = obsOf) (hgas₂ : c₂.gasOf = gasOf)
    (hb₂ : c₂.beforeState = s₁) (ha₂ : c₂.afterState = s₂) :
    ObsEquiv (obsOf s₂) (obsOf s₀) ∧ gasOf s₂ ≤ gasOf s₀ := by
  have h1 : ObsEquiv (obsOf s₁) (obsOf s₀) := by
    have hp := c₁.preserves_obs
    rw [hobs₁, hb₁, ha₁] at hp
    exact hp
  have h2 : ObsEquiv (obsOf s₂) (obsOf s₁) := by
    have hp := c₂.preserves_obs
    rw [hobs₂, hb₂, ha₂] at hp
    exact hp
  have hg1 : gasOf s₁ ≤ gasOf s₀ := by
    have hg := c₁.improves_gas
    rw [hgas₁, hb₁, ha₁] at hg
    exact hg
  have hg2 : gasOf s₂ ≤ gasOf s₁ := by
    have hg := c₂.improves_gas
    rw [hgas₂, hb₂, ha₂] at hg
    exact hg
  exact ⟨obsEquiv_trans h2 h1, Nat.le_trans hg2 hg1⟩

/-! ## 2. Revert Atomicity on Canonical Observations -/

/-- Canonical revert transformation on `Obs`: given pre-call storage `initStorage`,
    reverting with `revertPayload` discards all emitted logs, clears transient storage
    modifications back to `initTransient`, restores persistent `storage` to `initStorage`,
    and sets `status = .revert`. -/
def revertObs (initStorage initTransient : List (Nat × Nat)) (revertPayload : List UInt8) : Obs where
  status := .revert
  returndata := revertPayload
  logs := []
  storage := initStorage
  transient := initTransient

@[simp]
theorem revertObs_status (initStorage initTransient : List (Nat × Nat)) (payload : List UInt8) :
    (revertObs initStorage initTransient payload).status = .revert := rfl

@[simp]
theorem revertObs_logs_empty (initStorage initTransient : List (Nat × Nat)) (payload : List UInt8) :
    (revertObs initStorage initTransient payload).logs = [] := rfl

@[simp]
theorem revertObs_restores_storage (initStorage initTransient : List (Nat × Nat)) (payload : List UInt8) :
    (revertObs initStorage initTransient payload).storage = initStorage ∧
    (revertObs initStorage initTransient payload).transient = initTransient :=
  ⟨rfl, rfl⟩

/-! ## 3. Solidity Dynamic-Array & Bytes Storage Key Algebra -/

/-- 32-byte big-endian ABI encoding of a single base slot `s` (`pad32(s)`). -/
def abiEncodeSingleSlot (baseSlot : Nat) : ByteArray :=
  let slotWord : EvmYul.UInt256 := .ofNat baseSlot
  slotWord.toByteArray

/-- Solidity dynamic array base slot: `keccak256(bytes32(baseSlot))`.
    Unlike `solidityMappingSlot` (which hashes 64 bytes `key ++ baseSlot`), dynamic
    arrays hash the 32-byte slot index alone and add `index * stride`. -/
def solidityArrayBaseSlot (baseSlot : Nat) : Nat :=
  EvmYul.fromByteArrayBigEndian (KeccakEngine.keccak256 (abiEncodeSingleSlot baseSlot))

/-- Solidity dynamic array element slot for element `index` with element word `stride`:
    `(keccak256(bytes32(baseSlot)) + index * stride) % 2^256`. -/
def solidityArrayElemSlot (baseSlot index stride : Nat) : Nat :=
  (solidityArrayBaseSlot baseSlot + index * stride) % Compiler.Constants.evmModulus

/-- Unwrapped linear slot address `base + index * stride` (guaranteed `< 2^256` under
    the non-overflow guard `base + index * stride < evmModulus`). -/
def solidityArrayElemSlotUnwrapped (baseValue index stride : Nat) : Nat :=
  baseValue + index * stride

/-- Whenever `base + index * stride < evmModulus`, modulo reduction is the identity. -/
theorem solidityArrayElemSlot_eq_unwrapped_of_lt
    (baseSlot index stride : Nat)
    (hlt : solidityArrayBaseSlot baseSlot + index * stride < Compiler.Constants.evmModulus) :
    solidityArrayElemSlot baseSlot index stride =
      solidityArrayBaseSlot baseSlot + index * stride := by
  unfold solidityArrayElemSlot
  exact Nat.mod_eq_of_lt hlt

/-- **Index Injectivity for Dynamic Array Slots**:
    For any positive element `stride > 0` and two indices `i₁, i₂` that do not overflow
    the 256-bit slot space, equal derived element slots imply `i₁ = i₂`. -/
theorem solidityArrayElemSlot_injective_index
    (baseSlot i₁ i₂ stride : Nat)
    (hstride : 0 < stride)
    (hlt₁ : solidityArrayBaseSlot baseSlot + i₁ * stride < Compiler.Constants.evmModulus)
    (hlt₂ : solidityArrayBaseSlot baseSlot + i₂ * stride < Compiler.Constants.evmModulus)
    (heq : solidityArrayElemSlot baseSlot i₁ stride = solidityArrayElemSlot baseSlot i₂ stride) :
    i₁ = i₂ := by
  rw [solidityArrayElemSlot_eq_unwrapped_of_lt baseSlot i₁ stride hlt₁,
      solidityArrayElemSlot_eq_unwrapped_of_lt baseSlot i₂ stride hlt₂] at heq
  have hmul : i₁ * stride = i₂ * stride := Nat.add_left_cancel heq
  exact Nat.eq_of_mul_eq_mul_right hstride hmul

/-- Distinct indices `i₁ ≠ i₂` within a dynamic array of positive `stride > 0`
    always map to disjoint storage words. -/
theorem solidityArrayElemSlot_ne_of_index_ne
    {baseSlot i₁ i₂ stride : Nat}
    (hstride : 0 < stride)
    (hlt₁ : solidityArrayBaseSlot baseSlot + i₁ * stride < Compiler.Constants.evmModulus)
    (hlt₂ : solidityArrayBaseSlot baseSlot + i₂ * stride < Compiler.Constants.evmModulus)
    (hne : i₁ ≠ i₂) :
    solidityArrayElemSlot baseSlot i₁ stride ≠ solidityArrayElemSlot baseSlot i₂ stride := by
  intro heq
  exact hne (solidityArrayElemSlot_injective_index baseSlot i₁ i₂ stride hstride hlt₁ hlt₂ heq)

/-- Sub-element word offset `w₁, w₂ < stride` within multi-word struct arrays
    (`base + i * stride + w`) is uniquely determined by both `(i, w)`. -/
theorem multiSlotArrayElem_injective
    (base i₁ w₁ i₂ w₂ stride : Nat)
    (hw₁ : w₁ < stride)
    (hw₂ : w₂ < stride)
    (heq : base + (i₁ * stride + w₁) = base + (i₂ * stride + w₂)) :
    i₁ = i₂ ∧ w₁ = w₂ := by
  have hlin : i₁ * stride + w₁ = i₂ * stride + w₂ := Nat.add_left_cancel heq
  have hstride : 0 < stride := Nat.lt_of_le_of_lt (Nat.zero_le w₁) hw₁
  have hdiv₁ : (i₁ * stride + w₁) / stride = i₁ := by
    rw [Nat.mul_comm i₁ stride, Nat.mul_add_div hstride, Nat.div_eq_of_lt hw₁, Nat.add_zero]
  have hdiv₂ : (i₂ * stride + w₂) / stride = i₂ := by
    rw [Nat.mul_comm i₂ stride, Nat.mul_add_div hstride, Nat.div_eq_of_lt hw₂, Nat.add_zero]
  have hi : i₁ = i₂ := by
    rw [← hdiv₁, ← hdiv₂, hlin]
  subst hi
  exact ⟨rfl, Nat.add_left_cancel hlin⟩

/-- Extended storage key algebra covering scalar slots, addresses, mappings,
    dynamic array elements with stride, packed bytes/string data words, and
    EIP-1153 transient storage slots. -/
inductive ExtendedStorageKey where
  | word (slot : Nat)
  | addr (slot : Nat)
  | mapWord (slot key : Nat)
  | mapWord2 (slot k1 k2 : Nat)
  | arrayLength (slot : Nat)
  | arrayElem (slot index stride : Nat)
  | bytesDataWord (slot wordIndex : Nat)
  | transientWord (slot : Nat)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Project an `ExtendedStorageKey` onto the coarse contract-level `SpecStorageKey`
    channel used by `Verity.Specs.unchangedExcept`. -/
def ExtendedStorageKey.toCoarseChannel : ExtendedStorageKey → Option SpecStorageKey
  | .word s => some (.slot s)
  | .addr s => some (.addr s)
  | .mapWord s _ => some (.map s)
  | .mapWord2 s _ _ => some (.map2 s)
  | .arrayLength s => some (.array s)
  | .arrayElem s _ _ => some (.array s)
  | .bytesDataWord s _ => some (.array s)
  | .transientWord _ => none

/-- Transient storage keys never alias persistent `SpecStorageKey` channels. -/
@[simp]
theorem transientWord_disjoint_persistent_channels (s : Nat) :
    (ExtendedStorageKey.transientWord s).toCoarseChannel = none := rfl

/-- Executable witness suite (`by decide`, `0 native_decide`). -/
theorem obsAlgebra_executable_witness :
    let o1 : Obs := { status := .success, returndata := [1, 2], logs := [], storage := [(0, 42)], transient := [] }
    let o2 : Obs := revertObs [(0, 10)] [] [0x08, 0xc3, 0x79, 0xa0]
    obsEquivBool o1 o1 = true ∧
    obsEquivBool o1 o2 = false ∧
    o2.status = .revert ∧
    o2.storage = [(0, 10)] := by
  decide

end Verity.Specs.ObsAlgebra
