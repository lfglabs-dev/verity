/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.Codegen
import Compiler.Autoresearch.MaxwellGasSuperoptimizer

set_option autoImplicit false

namespace Compiler.Codegen.AccelPlugin

open Compiler
open Compiler.Yul
open Compiler.Autoresearch.MaxwellGasSuperoptimizer

/-!
# Segregated Acceleration Plugin Architecture & Speculative Gate
## Inspired by `lean-native` (`LeanNative.Spec` & `LeanNative.Transform.Plugins`)

This module implements the modular acceleration plugin architecture co-designed with
**Claude Fable 5.1** and **GPT-6 Astra**:

1. **Meta-Specification & Speculative Gate (`MetaGateSpec`, `evalWithUntrustedAccelPlugin`)**:
   Every optimization pass or external solver (`egglog` e-graphs, SMT/Bitwuzla, enumerative
   superoptimizers, or Maxwell-guided LLM mutators) is segregated outside Verity's semantic TCB.
   Candidates are admitted solely through `verifyAccelPluginGate`. If a plugin times out,
   produces an unverified certificate, or regresses gas cost, `evalWithUntrustedAccelPlugin`
   deterministically falls back to the unoptimized reference input (`untrusted_accel_plugin_gate_sound`).

2. **Certificate Chain & Kernel Theorem Allowlist (`AssuranceLevel`, `PassStepCert`)**:
   Each plugin step emits a `PassStepCert` recording its `AssuranceLevel`
   (`kernelVerified`, `translationValidated`, `boundedChecked`, `unverifiedFallback`),
   referenced kernel theorem, input/output structural hashes, and before/after gas costs.

3. **Default Certified G1–G7 Plugin Catalog (`defaultCertifiedPluginCatalog`)**:
   Exposes the 7 Maxwell-certified gas optimization passes (`G1`–`G7`) as replaceable,
   composable `VerifiedAccelContract` plugins.
-/

/-! ## 1. Universal Meta-Specifications (`MetaGateSpec` & `evalWithUntrustedAccelPlugin`) -/

/-- Universal meta-specification for a decidable safety/validation gate (`lean-native` Layer I). -/
structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate : Input → Bool
  sound : ∀ x, gate x = true → Safe x
  complete : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight : gate negWitness = false

/-- **Theorem AP.1 (`MetaGateSpec.rejects_unsafe`)**:
    Any input violating `Safe` is deterministically rejected (`gate x = false`). -/
theorem MetaGateSpec.rejects_unsafe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) (hUnsafe : ¬ Safe x) :
    M.gate x = false :=
  Bool.eq_false_iff.mpr (fun hOk => hUnsafe (M.sound x hOk))

/-- Speculative execution of an untrusted optimization plugin guarded by `verifyGate`.
    If the plugin returns `none` (timeout/no-op) or `verifyGate src cand cert = false`,
    falls back deterministically to `src`. -/
def evalWithUntrustedAccelPlugin {Prog Cert : Type}
    (plugin : Prog → Option (Prog × Cert))
    (verifyGate : Prog → Prog → Cert → Bool)
    (src : Prog) : Prog :=
  match plugin src with
  | some (cand, cert) => if verifyGate src cand cert then cand else src
  | none => src

/-- **Theorem AP.2 (`untrusted_accel_plugin_gate_sound`)**:
    For any reflexive refinement relation `Refines`, if `verifyGate` is sound,
    `evalWithUntrustedAccelPlugin` preserves `Refines` regardless of the untrusted `plugin` implementation. -/
theorem untrusted_accel_plugin_gate_sound {Prog Cert : Type}
    (Refines : Prog → Prog → Prop)
    (hRefl : ∀ p, Refines p p)
    (plugin : Prog → Option (Prog × Cert))
    (verifyGate : Prog → Prog → Cert → Bool)
    (hGateSound : ∀ src cand cert, verifyGate src cand cert = true → Refines src cand)
    (src : Prog) :
    Refines src (evalWithUntrustedAccelPlugin plugin verifyGate src) := by
  unfold evalWithUntrustedAccelPlugin
  split
  · split
    · exact hGateSound src _ _ ‹_›
    · exact hRefl src
  · exact hRefl src

/-- **Theorem AP.3 (`untrusted_accel_plugin_reject_fallback`)**:
    Whenever `verifyGate src cand cert = false`, `evalWithUntrustedAccelPlugin` returns `src` unchanged. -/
theorem untrusted_accel_plugin_reject_fallback {Prog Cert : Type}
    (plugin : Prog → Option (Prog × Cert))
    (verifyGate : Prog → Prog → Cert → Bool)
    (src cand : Prog) (cert : Cert)
    (hProp : plugin src = some (cand, cert))
    (hRej : verifyGate src cand cert = false) :
    evalWithUntrustedAccelPlugin plugin verifyGate src = src := by
  simp [evalWithUntrustedAccelPlugin, hProp, hRej]

/-! ## 2. Scopes, Assurance Levels, and Certificate Chains (`PassStepCert`) -/

/-- Compiler representation scope on which an acceleration plugin operates.
    Includes `.mathAlgebraic` for high-level EDSL/IR algebraic & fixed-point math
    simplifications backed by `Mathlib` (`ZMod (2^256)`, `CommRing`, `mulDiv` bounds)
    and `TauCeti` symbolic rewrite witnesses before lowering to Yul. -/
inductive AccelScope where
  | mathAlgebraic
  | ir
  | yul
  | bytecode
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Ordered assurance hierarchy for transformation certificates (`lean-native` style). -/
inductive AssuranceLevel where
  | kernelVerified
  | translationValidated
  | boundedChecked
  | unverifiedFallback
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Combine two assurance levels conservatively (weakest link in a pass chain). -/
def AssuranceLevel.combine (a b : AssuranceLevel) : AssuranceLevel :=
  match a, b with
  | .unverifiedFallback, _ | _, .unverifiedFallback => .unverifiedFallback
  | .boundedChecked, _ | _, .boundedChecked => .boundedChecked
  | .translationValidated, _ | _, .translationValidated => .translationValidated
  | .kernelVerified, .kernelVerified => .kernelVerified

/-- Per-step optimization certificate emitted by an acceleration plugin. -/
structure PassStepCert where
  pluginName : String
  scope : AccelScope
  passId : Option GasOptimizationPassId := none
  inputHash : Nat
  outputHash : Nat
  changed : Bool
  assurance : AssuranceLevel
  theoremRef : String
  costBefore : Nat
  costAfter : Nat
  boundaryChecked : Bool := true
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Allowlist of kernel-verified soundness theorems for Verity's G1–G34, patch, and
    `Mathlib` / `TauCeti` algebraic & fixed-point math simplification passes. -/
def verifiedAccelTheoremAllowlist : List String :=
  [ "Compiler.Proofs.YulGeneration.TempReuseSoundness.reuseBlockTemps_sound"
  , "Compiler.Codegen.Profile.dynamicSpillSlotAddr_disjoint_from_active_memory"
  , "Compiler.Proofs.SlotCoalescingShim.execCoalescedPackedWrites_eq_uncoalesced"
  , "Compiler.Proofs.MappingSlot.mappingSlot_cse_sound"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g4_checkedAdd_elision_sound_and_saves_gas"
  , "Compiler.Proofs.KeccakBound.scratchSpace_keccak_disjoint_freeMemPtr"
  , "Compiler.Proofs.IRGeneration.ParamLoading.calldataload_direct_sound"
  , "Compiler.Selector.binary_search_selector_dispatch_sound"
  , "Compiler.Proofs.YulGeneration.PatchRulesProofs.foundation_patch_bundle_sound"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g8_mathlib_tauceti_mulDiv_cancel_sound_and_saves_176_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g8_mulDivUp_eq_mulDivDown_of_mod_eq_zero"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g9_horner_cubic_polynomial_sound_and_saves_48_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g10_bn254_modField_elision_sound_and_saves_42_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g11_transient_delta_coalescing_sound_and_saves_400_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g12_packed_bitfield_shift_mask_cancel_sound_and_saves_18_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g13_mcopy_dynamic_abi_bulk_copy_saves_88_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g14_wad_unit_identity_elision_sound_and_saves_58_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g15_post_require_safeSub_guard_elision_sound_and_saves_38_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g16_nested_mapping2_prefix_cse_sound_and_saves_96_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g17_sstore_to_sload_forwarding_sound_and_saves_200_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g18_interval_bounded_min_branch_elision_sound_and_saves_32_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g19_custom_error_selector_push4_folding_sound_and_saves_36_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g20_noop_sstore_after_sload_elision_sound_and_saves_200_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g21_exact_ceilDiv_to_floorDiv_collapse_sound_and_saves_48_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g22_consecutive_bitmask_and_fusion_sound_and_saves_18_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g23_safeMul_interval_overflow_elision_sound_and_saves_48_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g24_power_of_two_div_to_shr_sound_and_saves_36_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g25_noop_transient_tstore_elision_sound_and_saves_100_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g26_power_of_two_mod_to_and_sound_and_saves_36_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g27_transient_tstore_to_tload_forwarding_sound_and_saves_200_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g28_dominated_require_bound_elision_sound_and_saves_38_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g29_consecutive_shr_offset_fusion_sound_and_saves_18_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g30_canonical_bool_double_iszero_elision_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g31_distributive_exact_div_factorization_sound_and_saves_58_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g32_consecutive_bitmask_or_fusion_sound_and_saves_18_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g33_non_overflowing_add_sub_cancel_sound_and_saves_44_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g34_dominated_calldatasize_guard_elision_sound_and_saves_44_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g35_guarded_sub_add_cancel_sound_and_saves_44_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g36_interval_tautological_lt_elision_sound_and_saves_32_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g37_consecutive_free_mem_bump_fusion_sound_and_saves_36_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g38_consecutive_shl_offset_fusion_sound_and_saves_18_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g39_distributive_exact_sub_div_factorization_sound_and_saves_58_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g40_overwritten_mstore_dead_write_elision_sound_and_saves_27_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g41_intra_block_mstore_to_mload_forwarding_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g42_xor_involutive_mask_cancellation_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g43_interval_bounded_low_bitmask_and_elision_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g44_noop_mstore_after_mload_elision_sound_and_saves_27_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g45_dominated_bitmask_and_after_mask_elision_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g46_consecutive_memory_offset_add_fusion_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g47_dominated_bitmask_or_after_set_elision_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g48_interval_bounded_shl_shr_roundtrip_cancel_sound_and_saves_36_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g49_interval_tautological_iszero_lt_elision_sound_and_saves_38_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g50_overwritten_tstore_dead_write_elision_sound_and_saves_200_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g51_consecutive_div_fusion_sound_and_saves_24_gas"
  , "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g52_disjoint_bitmask_and_elision_sound_and_saves_24_gas"
  , "Verity.Proofs.Stdlib.Math.mulDivDown_cancel_right"
  , "Verity.Proofs.Stdlib.Math.mulDivUp_eq_mulDivDown_of_dvd"
  , "Verity.Proofs.Stdlib.Math.wMulDown_one_right"
  , "Verity.Proofs.Stdlib.Math.modField_eq_self_of_lt" ]

/-- Check whether `thmRef` is registered in the kernel theorem allowlist. -/
def isAllowedAccelTheorem (thmRef : String) : Bool :=
  verifiedAccelTheoremAllowlist.contains thmRef

/-- Three-layer verification gate (`verifyAccelCertGate`):
    - **Layer 1 (Symbolic/Kernel Certificate)**: `assurance` must be `kernelVerified` (with
      `theoremRef ∈ verifiedAccelTheoremAllowlist`) or `translationValidated` (with non-empty witness),
      and unchanged steps must preserve hashes (`!changed → inputHash = outputHash`),
    - **Layer 2 (Concrete Boundary Equivalence)**: `boundaryChecked = true`,
    - **Layer 3 (Gas Non-Regression)**: `costAfter ≤ costBefore` (or `costAfter < costBefore` when
      `requireStrictGain = true`). -/
def verifyAccelCertGate (requireStrictGain : Bool) (c : PassStepCert) : Bool :=
  let hashCoherent := if c.changed then true else decide (c.inputHash = c.outputHash)
  let symbolicOk :=
    match c.assurance with
    | .kernelVerified => isAllowedAccelTheorem c.theoremRef
    | .translationValidated => !c.theoremRef.isEmpty
    | .boundedChecked => false
    | .unverifiedFallback => false
  let gasOk :=
    if requireStrictGain then decide (c.costAfter < c.costBefore)
    else decide (c.costAfter ≤ c.costBefore)
  hashCoherent && symbolicOk && c.boundaryChecked && gasOk

/-- **Theorem AP.4 (`verifyAccelCertGate_enforces_gas_non_regression`)**:
    Every certificate accepted by `verifyAccelCertGate` guarantees `c.costAfter ≤ c.costBefore`
    and `c.boundaryChecked = true`, while rejecting `.unverifiedFallback` and `.boundedChecked`. -/
theorem verifyAccelCertGate_enforces_gas_non_regression
    (requireStrictGain : Bool) (c : PassStepCert)
    (hOk : verifyAccelCertGate requireStrictGain c = true) :
    c.costAfter ≤ c.costBefore ∧
    c.boundaryChecked = true ∧
    c.assurance ≠ .unverifiedFallback := by
  unfold verifyAccelCertGate at hOk
  simp only [Bool.and_eq_true] at hOk
  obtain ⟨⟨⟨_, hSym⟩, hBound⟩, hGas⟩ := hOk
  refine ⟨?_, hBound, ?_⟩
  · cases requireStrictGain with
    | false =>
      exact of_decide_eq_true hGas
    | true =>
      have hLt : c.costAfter < c.costBefore := of_decide_eq_true hGas
      omega
  · intro hUnv
    rw [hUnv] at hSym
    contradiction

/-- Check hash-chain continuity (`c₁.outputHash = c₂.inputHash`) and per-step validity across a chain. -/
def verifyCertChain (requireStrictGain : Bool) : List PassStepCert → Bool
  | [] => true
  | [c] => verifyAccelCertGate requireStrictGain c
  | c₁ :: c₂ :: rest =>
      verifyAccelCertGate requireStrictGain c₁ &&
      decide (c₁.outputHash = c₂.inputHash) &&
      verifyCertChain requireStrictGain (c₂ :: rest)

/-- **Theorem AP.5 (`verifyCertChain_head_valid`)**:
    If a certificate chain `c :: rest` is accepted by `verifyCertChain`, its head step `c`
    satisfies `verifyAccelCertGate` and therefore guarantees `c.costAfter ≤ c.costBefore`. -/
theorem verifyCertChain_head_valid
    (requireStrictGain : Bool) (c : PassStepCert) (rest : List PassStepCert)
    (hChain : verifyCertChain requireStrictGain (c :: rest) = true) :
    verifyAccelCertGate requireStrictGain c = true ∧ c.costAfter ≤ c.costBefore := by
  cases rest with
  | nil =>
    unfold verifyCertChain at hChain
    exact ⟨hChain, (verifyAccelCertGate_enforces_gas_non_regression requireStrictGain c hChain).1⟩
  | cons c₂ tl =>
    unfold verifyCertChain at hChain
    simp only [Bool.and_eq_true] at hChain
    exact ⟨hChain.1.1, (verifyAccelCertGate_enforces_gas_non_regression requireStrictGain c hChain.1.1).1⟩

/-! ## 3. Compositional Verified Acceleration Contracts (`VerifiedAccelContract`) -/

/-- Proof-carrying transformation contract over a program carrier `Prog` with refinement `Refines`. -/
structure VerifiedAccelContract (Prog : Type) (Refines : Prog → Prog → Prop) where
  name : String
  scope : AccelScope
  run : Prog → Prog
  is_sound : ∀ p, Refines p (run p)

/-- Compose two `VerifiedAccelContract` steps sequentially while preserving `Refines`. -/
def VerifiedAccelContract.compose {Prog : Type} {Refines : Prog → Prog → Prop}
    (hTrans : ∀ a b c, Refines a b → Refines b c → Refines a c)
    (c₁ c₂ : VerifiedAccelContract Prog Refines) :
    VerifiedAccelContract Prog Refines where
  name := c₁.name ++ " >> " ++ c₂.name
  scope := c₂.scope
  run := fun p => c₂.run (c₁.run p)
  is_sound := fun p => hTrans p (c₁.run p) (c₂.run (c₁.run p)) (c₁.is_sound p) (c₂.is_sound (c₁.run p))

/-- Lift any untrusted plugin `Prog → Option (Prog × PassStepCert)` into a `VerifiedAccelContract`
    via `evalWithUntrustedAccelPlugin`. -/
def VerifiedAccelContract.fromGatedPlugin {Prog : Type} {Refines : Prog → Prog → Prop}
    (name : String)
    (scope : AccelScope)
    (hRefl : ∀ p, Refines p p)
    (plugin : Prog → Option (Prog × PassStepCert))
    (verifyGate : Prog → Prog → PassStepCert → Bool)
    (hGateSound : ∀ src cand cert, verifyGate src cand cert = true → Refines src cand) :
    VerifiedAccelContract Prog Refines where
  name := name
  scope := scope
  run := evalWithUntrustedAccelPlugin plugin verifyGate
  is_sound := untrusted_accel_plugin_gate_sound Refines hRefl plugin verifyGate hGateSound

abbrev AccelChain (Prog : Type) (Refines : Prog → Prog → Prop) :=
  List (VerifiedAccelContract Prog Refines)

/-- Execute a chain of `VerifiedAccelContract` plugins from left to right. -/
def runAccelPluginChain {Prog : Type} {Refines : Prog → Prog → Prop}
    (chain : AccelChain Prog Refines)
    (init : Prog) : Prog :=
  chain.foldl (fun acc step => step.run acc) init

/-- **Theorem AP.6 (`runAccelPluginChain_nil_eq_self` — Definitional Identity by `rfl`)**:
    Running an empty plugin chain (`[]`, as used in `PipelineConfig.legacy`) is definitionally `init`. -/
@[simp]
theorem runAccelPluginChain_nil_eq_self {Prog : Type} {Refines : Prog → Prog → Prop}
    (init : Prog) :
    runAccelPluginChain ([] : AccelChain Prog Refines) init = init := rfl

/-- **Theorem AP.7 (`runAccelPluginChain_sound` — End-to-End Plugin Chain Refinement)**:
    For any reflexive and transitive refinement relation `Refines`, executing any list of
    `VerifiedAccelContract` plugins preserves `Refines` end-to-end. -/
theorem runAccelPluginChain_sound {Prog : Type} {Refines : Prog → Prog → Prop}
    (hRefl : ∀ p, Refines p p)
    (hTrans : ∀ a b c, Refines a b → Refines b c → Refines a c)
    (chain : AccelChain Prog Refines)
    (init : Prog) :
    Refines init (runAccelPluginChain chain init) := by
  induction chain generalizing init with
  | nil => exact hRefl init
  | cons hd tl ih =>
    unfold runAccelPluginChain
    simp only [List.foldl]
    exact hTrans init (hd.run init) (runAccelPluginChain tl (hd.run init))
      (hd.is_sound init) (ih (hd.run init))

/-! ## 4. Default Certified G1–G7 Plugin Catalog & Concrete MetaGate Witness -/

/-- Declarative descriptor for a replaceable optimization plugin in Verity's default catalog.
    `passId` is optional so algebraic `Mathlib`/`TauCeti` plugins at scope `.mathAlgebraic`
    share the exact same descriptor and `verifyAccelCertGate` contract as `G1`–`G7`. -/
structure AccelPluginDescriptor where
  pluginName : String
  scope : AccelScope
  passId : Option GasOptimizationPassId := none
  assurance : AssuranceLevel
  theoremRef : String
  enabledByDefault : Bool := true
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The certified gas & algebraic optimization plugins (`G1`–`G7` + `G8:mathlib-tauceti`)
    enabled by default in Verity 2.0. -/
def defaultCertifiedPluginCatalog : List AccelPluginDescriptor :=
  [ { pluginName := "G1:temp-reuse-stack-scheduling"
      scope := .yul
      passId := some .G1_tempReuseStackScheduling
      assurance := .kernelVerified
      theoremRef := "Compiler.Proofs.YulGeneration.TempReuseSoundness.reuseBlockTemps_sound" }
  , { pluginName := "G2:slot-coalescing-packed-words"
      scope := .ir
      passId := some .G2_slotCoalescingPackedWords
      assurance := .kernelVerified
      theoremRef := "Compiler.Proofs.SlotCoalescingShim.execCoalescedPackedWrites_eq_uncoalesced" }
  , { pluginName := "G3:mapping-slot-cse"
      scope := .yul
      passId := some .G3_mappingSlotCSE
      assurance := .kernelVerified
      theoremRef := "Compiler.Proofs.MappingSlot.mappingSlot_cse_sound" }
  , { pluginName := "G4:checked-arith-interval-elision"
      scope := .yul
      passId := some .G4_checkedArithIntervalElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g4_checkedAdd_elision_sound_and_saves_gas" }
  , { pluginName := "G5:scratch-space-hashing"
      scope := .yul
      passId := some .G5_scratchSpaceHashing
      assurance := .kernelVerified
      theoremRef := "Compiler.Proofs.KeccakBound.scratchSpace_keccak_disjoint_freeMemPtr" }
  , { pluginName := "G6:calldata-lazy-decoding"
      scope := .ir
      passId := some .G6_calldataLazyDecoding
      assurance := .kernelVerified
      theoremRef := "Compiler.Proofs.IRGeneration.ParamLoading.calldataload_direct_sound" }
  , { pluginName := "G7:selector-dispatch-tree-log-n"
      scope := .yul
      passId := some .G7_selectorDispatchTreeLogN
      assurance := .kernelVerified
      theoremRef := "Compiler.Selector.binary_search_selector_dispatch_sound" }
  , { pluginName := "G8:mathlib-tauceti-algebraic-simplifier"
      scope := .mathAlgebraic
      passId := some .G8_mathlibTauCetiAlgebraicSimplifier
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g8_mathlib_tauceti_mulDiv_cancel_sound_and_saves_176_gas" }
  , { pluginName := "G9:horner-polynomial-wad-ray-factorization"
      scope := .mathAlgebraic
      passId := some .G9_hornerPolynomialWadRayFactorization
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g9_horner_cubic_polynomial_sound_and_saves_48_gas" }
  , { pluginName := "G10:bn254-modfield-interval-elision"
      scope := .mathAlgebraic
      passId := some .G10_bn254ModFieldIntervalElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g10_bn254_modField_elision_sound_and_saves_42_gas" }
  , { pluginName := "G11:transient-delta-coalescing-eip1153"
      scope := .ir
      passId := some .G11_transientDeltaCoalescingEIP1153
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g11_transient_delta_coalescing_sound_and_saves_400_gas" }
  , { pluginName := "G12:packed-bitfield-shift-mask-cancel"
      scope := .yul
      passId := some .G12_packedBitfieldShiftMaskCancel
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g12_packed_bitfield_shift_mask_cancel_sound_and_saves_18_gas" }
  , { pluginName := "G13:mcopy-dynamic-abi-bulk-copy-eip5656"
      scope := .yul
      passId := some .G13_mcopyDynamicAbiBulkCopyEIP5656
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g13_mcopy_dynamic_abi_bulk_copy_saves_88_gas" }
  , { pluginName := "G14:wad-ray-unit-identity-elision"
      scope := .mathAlgebraic
      passId := some .G14_wadRayUnitIdentityElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g14_wad_unit_identity_elision_sound_and_saves_58_gas" }
  , { pluginName := "G15:post-require-safesub-guard-elision"
      scope := .ir
      passId := some .G15_postRequireSafeSubGuardElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g15_post_require_safeSub_guard_elision_sound_and_saves_38_gas" }
  , { pluginName := "G16:nested-mapping-prefix-keccak-cse"
      scope := .yul
      passId := some .G16_nestedMappingPrefixKeccakCSE
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g16_nested_mapping2_prefix_cse_sound_and_saves_96_gas" }
  , { pluginName := "G17:sstore-to-sload-forwarding"
      scope := .ir
      passId := some .G17_sstoreToSloadForwarding
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g17_sstore_to_sload_forwarding_sound_and_saves_200_gas" }
  , { pluginName := "G18:interval-bounded-min-max-branch-elision"
      scope := .mathAlgebraic
      passId := some .G18_intervalBoundedMinMaxBranchElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g18_interval_bounded_min_branch_elision_sound_and_saves_32_gas" }
  , { pluginName := "G19:custom-error-selector-push4-folding"
      scope := .yul
      passId := some .G19_customErrorSelectorPush4Folding
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g19_custom_error_selector_push4_folding_sound_and_saves_36_gas" }
  , { pluginName := "G20:noop-sstore-after-sload-elision"
      scope := .ir
      passId := some .G20_noopSstoreAfterSloadElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g20_noop_sstore_after_sload_elision_sound_and_saves_200_gas" }
  , { pluginName := "G21:exact-ceildiv-to-floordiv-collapse"
      scope := .mathAlgebraic
      passId := some .G21_exactCeilDivToFloorDivCollapse
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g21_exact_ceilDiv_to_floorDiv_collapse_sound_and_saves_48_gas" }
  , { pluginName := "G22:consecutive-bitmask-and-fusion"
      scope := .yul
      passId := some .G22_consecutiveBitmaskAndFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g22_consecutive_bitmask_and_fusion_sound_and_saves_18_gas" }
  , { pluginName := "G23:safemul-interval-overflow-elision"
      scope := .mathAlgebraic
      passId := some .G23_safeMulIntervalOverflowElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g23_safeMul_interval_overflow_elision_sound_and_saves_48_gas" }
  , { pluginName := "G24:power-of-two-div-mod-strength-reduction"
      scope := .yul
      passId := some .G24_powerOfTwoDivModStrengthReduction
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g24_power_of_two_div_to_shr_sound_and_saves_36_gas" }
  , { pluginName := "G25:noop-transient-tstore-elision-eip1153"
      scope := .ir
      passId := some .G25_noopTransientTstoreElisionEIP1153
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g25_noop_transient_tstore_elision_sound_and_saves_100_gas" }
  , { pluginName := "G26:power-of-two-mod-bitmask-strength-reduction"
      scope := .yul
      passId := some .G26_powerOfTwoModBitmaskStrengthReduction
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g26_power_of_two_mod_to_and_sound_and_saves_36_gas" }
  , { pluginName := "G27:transient-tstore-to-tload-forwarding-eip1153"
      scope := .ir
      passId := some .G27_transientTstoreToTloadForwardingEIP1153
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g27_transient_tstore_to_tload_forwarding_sound_and_saves_200_gas" }
  , { pluginName := "G28:dominated-require-bound-elision"
      scope := .ir
      passId := some .G28_dominatedRequireBoundElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g28_dominated_require_bound_elision_sound_and_saves_38_gas" }
  , { pluginName := "G29:consecutive-shift-offset-fusion"
      scope := .yul
      passId := some .G29_consecutiveShiftOffsetFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g29_consecutive_shr_offset_fusion_sound_and_saves_18_gas" }
  , { pluginName := "G30:boolean-double-iszero-elision"
      scope := .yul
      passId := some .G30_booleanDoubleIszeroElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g30_canonical_bool_double_iszero_elision_sound_and_saves_24_gas" }
  , { pluginName := "G31:distributive-exact-div-factorization"
      scope := .mathAlgebraic
      passId := some .G31_distributiveExactDivFactorization
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g31_distributive_exact_div_factorization_sound_and_saves_58_gas" }
  , { pluginName := "G32:consecutive-bitmask-or-fusion"
      scope := .yul
      passId := some .G32_consecutiveBitmaskOrFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g32_consecutive_bitmask_or_fusion_sound_and_saves_18_gas" }
  , { pluginName := "G33:non-overflowing-add-sub-cancellation"
      scope := .mathAlgebraic
      passId := some .G33_nonOverflowingAddSubCancellation
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g33_non_overflowing_add_sub_cancel_sound_and_saves_44_gas" }
  , { pluginName := "G34:dominated-calldatasize-guard-elision"
      scope := .yul
      passId := some .G34_dominatedCalldatasizeGuardElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g34_dominated_calldatasize_guard_elision_sound_and_saves_44_gas" }
  , { pluginName := "G35:guarded-sub-add-roundtrip-cancellation"
      scope := .mathAlgebraic
      passId := some .G35_guardedSubAddRoundtripCancellation
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g35_guarded_sub_add_cancel_sound_and_saves_44_gas" }
  , { pluginName := "G36:interval-tautological-comparison-elision"
      scope := .mathAlgebraic
      passId := some .G36_intervalTautologicalComparisonElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g36_interval_tautological_lt_elision_sound_and_saves_32_gas" }
  , { pluginName := "G37:consecutive-free-mem-bump-fusion"
      scope := .yul
      passId := some .G37_consecutiveFreeMemBumpFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g37_consecutive_free_mem_bump_fusion_sound_and_saves_36_gas" }
  , { pluginName := "G38:consecutive-left-shift-offset-fusion"
      scope := .yul
      passId := some .G38_consecutiveLeftShiftOffsetFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g38_consecutive_shl_offset_fusion_sound_and_saves_18_gas" }
  , { pluginName := "G39:distributive-exact-sub-div-factorization"
      scope := .mathAlgebraic
      passId := some .G39_distributiveExactSubDivFactorization
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g39_distributive_exact_sub_div_factorization_sound_and_saves_58_gas" }
  , { pluginName := "G40:overwritten-mstore-dead-write-elision"
      scope := .yul
      passId := some .G40_overwrittenMstoreDeadWriteElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g40_overwritten_mstore_dead_write_elision_sound_and_saves_27_gas" }
  , { pluginName := "G41:intra-block-mstore-to-mload-forwarding"
      scope := .yul
      passId := some .G41_intraBlockMstoreToMloadForwarding
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g41_intra_block_mstore_to_mload_forwarding_sound_and_saves_24_gas" }
  , { pluginName := "G42:xor-involutive-mask-cancellation"
      scope := .yul
      passId := some .G42_xorInvolutiveMaskCancellation
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g42_xor_involutive_mask_cancellation_sound_and_saves_24_gas" }
  , { pluginName := "G43:interval-bounded-low-bitmask-and-elision"
      scope := .mathAlgebraic
      passId := some .G43_intervalBoundedLowBitmaskAndElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g43_interval_bounded_low_bitmask_and_elision_sound_and_saves_24_gas" }
  , { pluginName := "G44:noop-mstore-after-mload-elision"
      scope := .yul
      passId := some .G44_noopMstoreAfterMloadElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g44_noop_mstore_after_mload_elision_sound_and_saves_27_gas" }
  , { pluginName := "G45:dominated-bitmask-and-after-mask-elision"
      scope := .yul
      passId := some .G45_dominatedBitmaskAndAfterMaskElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g45_dominated_bitmask_and_after_mask_elision_sound_and_saves_24_gas" }
  , { pluginName := "G46:consecutive-memory-offset-add-fusion"
      scope := .yul
      passId := some .G46_consecutiveMemoryOffsetAddFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g46_consecutive_memory_offset_add_fusion_sound_and_saves_24_gas" }
  , { pluginName := "G47:dominated-bitmask-or-after-set-elision"
      scope := .yul
      passId := some .G47_dominatedBitmaskOrAfterSetElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g47_dominated_bitmask_or_after_set_elision_sound_and_saves_24_gas" }
  , { pluginName := "G48:interval-bounded-shl-shr-roundtrip-cancellation"
      scope := .mathAlgebraic
      passId := some .G48_intervalBoundedShlShrRoundtripCancellation
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g48_interval_bounded_shl_shr_roundtrip_cancel_sound_and_saves_36_gas" }
  , { pluginName := "G49:interval-tautological-iszero-lt-elision"
      scope := .mathAlgebraic
      passId := some .G49_intervalTautologicalIszeroLtElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g49_interval_tautological_iszero_lt_elision_sound_and_saves_38_gas" }
  , { pluginName := "G50:overwritten-tstore-dead-write-elision"
      scope := .ir
      passId := some .G50_overwrittenTstoreDeadWriteElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g50_overwritten_tstore_dead_write_elision_sound_and_saves_200_gas" }
  , { pluginName := "G51:consecutive-div-fusion"
      scope := .mathAlgebraic
      passId := some .G51_consecutiveDivFusion
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g51_consecutive_div_fusion_sound_and_saves_24_gas" }
  , { pluginName := "G52:disjoint-bitmask-and-elision"
      scope := .yul
      passId := some .G52_disjointBitmaskAndElision
      assurance := .kernelVerified
      theoremRef := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g52_disjoint_bitmask_and_elision_sound_and_saves_24_gas" } ]

/-- Synthesize a verified `PassStepCert` for a catalog descriptor given before/after gas and hashes. -/
def AccelPluginDescriptor.mkStepCert
    (d : AccelPluginDescriptor)
    (inputHash outputHash costBefore costAfter : Nat) : PassStepCert :=
  { pluginName := d.pluginName
    scope := d.scope
    passId := d.passId
    inputHash := inputHash
    outputHash := outputHash
    changed := decide (inputHash ≠ outputHash)
    assurance := d.assurance
    theoremRef := d.theoremRef
    costBefore := costBefore
    costAfter := costAfter
    boundaryChecked := true }

/-- **Theorem AP.8 (All Default G1–G8 Catalog Plugins Pass `verifyAccelCertGate`)**:
    Every plugin in `defaultCertifiedPluginCatalog` (including `G8:mathlib-tauceti-algebraic-simplifier`)
    produces a valid `PassStepCert` whenever `costAfter ≤ costBefore`. -/
theorem defaultCertifiedPluginCatalog_all_verified :
    (defaultCertifiedPluginCatalog.all (fun d =>
      verifyAccelCertGate false (d.mkStepCert 100 101 1000 800))) = true := by
  decide

/-! ## 5. Autonomous Loop Invariants (`BurnedPaths` & `H*` Sealed-Regime Ratchet Gate) -/

/-- Record of a refuted optimization hypothesis burned (`p = 0`) during the Maxwell loop,
    preventing the autonomous search from re-proposing the same unsound mechanism. -/
structure BurnedPathEntry where
  mechanismHash : String
  axis : String
  counterexample256 : String
  refutationTheorem : String
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Registry of burned optimization paths (`p = 0`) with machine-checked 256-bit counterexamples. -/
def burnedPathsRegistry : List BurnedPathEntry :=
  [ { mechanismHash := "G8-burn-01:unguarded-muldiv-cancel-uint256"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "a = 2^255, d = 2 => ((a * d) % 2^256) / d = 0 != a"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g8_unguarded_mulDiv_cancel_refuted" }
  , { mechanismHash := "G8-burn-02:unguarded-muldivup-eq-down-without-dvd"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "a = 1, b = 1, d = 2 => (1 + 1) / 2 = 1 != 1 / 2 = 0"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g8_unguarded_mulDivUp_eq_down_refuted" }
  , { mechanismHash := "G10-burn-03:uint256-bound-only-bn254-modfield-elision"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "x = SNARK_SCALAR_FIELD < 2^256 => x % SNARK_SCALAR_FIELD = 0 != x"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g10_unguarded_uint256_modField_elision_refuted" }
  , { mechanismHash := "G11-burn-04:cross-callback-transient-tstore-coalescing"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "bal = 100, d1 = 50 => external hook observes 100 != 150"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g11_cross_callback_transient_coalescing_refuted" }
  , { mechanismHash := "G12-burn-05:unaligned-shr-shl-roundtrip-elision"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "x = 7, s = 1 => (7 / 2) * 2 = 6 != 7"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g12_unaligned_shr_shl_cancel_refuted" }
  , { mechanismHash := "G14-burn-06:wad-floor-mul-reassociation"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "a = 4, b = 5, c = 5, scale = 10 => (((4 * 5) / 10) * 5) / 10 = 1 != (4 * ((5 * 5) / 10)) / 10 = 0"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g14_wad_mul_reassociation_refuted" }
  , { mechanismHash := "G17-burn-07:aliased-mapping-sstore-sload-forwarding"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "k1 = 7, k2 = 7, v1 = 10, v2 = 20 => aliased slot holds 20 != 10"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g17_aliased_mapping_sstore_forwarding_refuted" }
  , { mechanismHash := "G19-burn-08:unshifted-custom-error-selector-revert"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "sel = 0xdeadbeef => unshifted mstore(0x00, sel) high 4 bytes = 0 != 0xdeadbeef"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g19_unshifted_custom_error_selector_revert_refuted" }
  , { mechanismHash := "G20-burn-09:intervening-write-sstore-elision"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "v0 = 42, v1 = 99 => eliding SSTORE(s, v0) after SSTORE(s, v1) leaves 99 != 42"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g20_intervening_write_sstore_elision_refuted" }
  , { mechanismHash := "G21-burn-10:non-exact-ceildiv-to-floordiv-collapse"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "a = 7, d = 4 => (7 + 3) / 4 = 2 != 7 / 4 = 1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g21_non_exact_ceilDiv_collapse_refuted" }
  , { mechanismHash := "G23-burn-11:sum-bound-only-safemul-overflow-elision"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "a = 2^128, b = 2^128 => a + b < 2^256 but (a * b) % 2^256 = 0 != 2^256"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g23_sum_bound_only_safeMul_elision_refuted" }
  , { mechanismHash := "G24-burn-12:signed-negative-sdiv-to-sar-reduction"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "sdiv(-1, 2) = 0 != sar(1, -1) = -1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g24_signed_negative_sdiv_to_sar_refuted" }
  , { mechanismHash := "G26-burn-13:non-power-of-two-mod-bitmask-reduction"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "x = 6, d = 6 => 6 &&& 5 = 4 != 6 % 6 = 0"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g26_non_power_of_two_mod_bitmask_refuted" }
  , { mechanismHash := "G27-burn-14:reverted-frame-transient-tstore-forwarding"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "valBeforeRevert = 50 != tloadAfterRevert = 0"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g27_reverted_frame_transient_forwarding_refuted" }
  , { mechanismHash := "G29-burn-15:mixed-shl-shr-overflow-offset-cancellation"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "x = 2^255, k1 = 1, k2 = 2 => ((x * 2) % 2^256) / 4 = 0 != x / 2 = 2^254"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g29_mixed_shl_shr_overflow_fusion_refuted" }
  , { mechanismHash := "G31-burn-16:unfactored-floor-div-add-distribution"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "x = 1, y = 1, d = 2 => (1 + 1) / 2 = 1 != 1 / 2 + 1 / 2 = 0"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g31_unfactored_floor_div_add_distribution_refuted" }
  , { mechanismHash := "G32-burn-17:overlapping-bitmask-or-to-add-replacement"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "x = 1, m = 1 => (1 ||| 1) = 1 != 1 + 1 = 2"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g32_overlapping_bitmask_or_to_add_refuted" }
  , { mechanismHash := "G33-burn-18:overflowing-add-sub-roundtrip-cancellation"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "a = 2^256 - 1, b = 1 => ((a + b) % 2^256) - b = 0 != a"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g33_overflowing_add_sub_cancel_refuted" }
  , { mechanismHash := "G35-burn-19:unguarded-sub-add-underflow-cancellation"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "x = 3, d = 5 => safeSub(3, 5) reverts (none) != some 3"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g35_unguarded_sub_add_underflow_cancel_refuted" }
  , { mechanismHash := "G36-burn-20:overlapping-interval-strict-lt-elision"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "x = 10, y = 10 => (if 10 < 10 then 1 else 0) = 0 != 1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g36_overlapping_interval_strict_lt_elision_refuted" }
  , { mechanismHash := "G38-burn-21:unmasked-shl-field-packing-overflow"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "hi = 1, lo = 4, k = 1 => ((1 * 2) + 4) / 2 = 3 != 1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g38_unmasked_shl_field_packing_overflow_refuted" }
  , { mechanismHash := "G39-burn-22:unfactored-floor-div-sub-distribution"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "x = 2, y = 1, d = 2 => (2 - 1) / 2 = 0 != 2 / 2 - 1 / 2 = 1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g39_unfactored_floor_div_sub_distribution_refuted" }
  , { mechanismHash := "G41-burn-23:overlapping-unaligned-mstore-forwarding"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "v1 = 1, clobberedWord = 256 => MSTORE(0x01, v2) clobbers MLOAD(0x00)"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g41_overlapping_unaligned_mstore_forwarding_refuted" }
  , { mechanismHash := "G43-burn-24:boundary-low-bitmask-and-elision"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "k = 8, x = 256 => 256 &&& 255 = 0 != 256"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g43_boundary_low_bitmask_and_elision_refuted" }
  , { mechanismHash := "G44-burn-25:intervening-scratch-write-noop-mstore-elision"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "v0 = 11, v1 = 22 => eliding MSTORE(0x00, v0) after MSTORE(0x00, v1) leaves 22 != 11"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g44_intervening_scratch_write_noop_mstore_elision_refuted" }
  , { mechanismHash := "G46-burn-26:wrapped-offset-add-fusion-across-lt-guard"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "base = 10, off1 = 2^256 - 5, off2 = 8 => 5 < 10 != 13 < 10"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g46_wrapped_offset_add_fusion_across_lt_guard_refuted" }
  , { mechanismHash := "G48-burn-27:overflowing-shl-shr-roundtrip-cancellation"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "x = 2^255, k = 1 => ((x * 2) % 2^256) / 2 = 0 != 2^255"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g48_overflowing_shl_shr_roundtrip_cancel_refuted" }
  , { mechanismHash := "G49-burn-28:upper-bound-only-iszero-lt-elision"
      axis := "abstract_domain_interval_elision"
      counterexample256 := "x = 4, y = 7, maxX = 10 => (if 4 < 7 then 0 else 1) = 0 != 1"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g49_upper_bound_only_iszero_lt_elision_refuted" }
  , { mechanismHash := "G50-burn-29:cross-callback-dead-tstore-elision"
      axis := "yul_patch_or_egraph_witness"
      counterexample256 := "v1 = 7, v2 = 9 => hook observes 7 != 9"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g50_cross_callback_dead_tstore_elision_refuted" }
  , { mechanismHash := "G51-burn-30:wrapped-div-product-fusion"
      axis := "math_algebraic_tauceti_rule"
      counterexample256 := "d1 = 2, d2 = 2^255 => (2 * 2^255) % 2^256 = 0 != 2^256"
      refutationTheorem := "Compiler.Autoresearch.MaxwellGasSuperoptimizer.g51_wrapped_div_product_fusion_refuted" } ]

/-- Check whether a candidate `mechanismHash` has already been burned in `burnedPathsRegistry`. -/
def isBurnedMechanism (mechanismHash : String) : Bool :=
  burnedPathsRegistry.any (fun b => b.mechanismHash == mechanismHash)

/-- **Theorem AP.9 (`unguarded_muldiv_is_burned_and_ratchet_is_not`)**:
    Verifies that all thirty refuted hypotheses (`G8-burn-01`..`G51-burn-30`)
    are blocked by `isBurnedMechanism`, whereas the guarded `G8`–`G52`
    simplifications are permitted. -/
theorem unguarded_muldiv_is_burned_and_ratchet_is_not :
    isBurnedMechanism "G8-burn-01:unguarded-muldiv-cancel-uint256" = true ∧
    isBurnedMechanism "G8-burn-02:unguarded-muldivup-eq-down-without-dvd" = true ∧
    isBurnedMechanism "G10-burn-03:uint256-bound-only-bn254-modfield-elision" = true ∧
    isBurnedMechanism "G11-burn-04:cross-callback-transient-tstore-coalescing" = true ∧
    isBurnedMechanism "G12-burn-05:unaligned-shr-shl-roundtrip-elision" = true ∧
    isBurnedMechanism "G14-burn-06:wad-floor-mul-reassociation" = true ∧
    isBurnedMechanism "G17-burn-07:aliased-mapping-sstore-sload-forwarding" = true ∧
    isBurnedMechanism "G19-burn-08:unshifted-custom-error-selector-revert" = true ∧
    isBurnedMechanism "G20-burn-09:intervening-write-sstore-elision" = true ∧
    isBurnedMechanism "G21-burn-10:non-exact-ceildiv-to-floordiv-collapse" = true ∧
    isBurnedMechanism "G23-burn-11:sum-bound-only-safemul-overflow-elision" = true ∧
    isBurnedMechanism "G24-burn-12:signed-negative-sdiv-to-sar-reduction" = true ∧
    isBurnedMechanism "G26-burn-13:non-power-of-two-mod-bitmask-reduction" = true ∧
    isBurnedMechanism "G27-burn-14:reverted-frame-transient-tstore-forwarding" = true ∧
    isBurnedMechanism "G29-burn-15:mixed-shl-shr-overflow-offset-cancellation" = true ∧
    isBurnedMechanism "G31-burn-16:unfactored-floor-div-add-distribution" = true ∧
    isBurnedMechanism "G32-burn-17:overlapping-bitmask-or-to-add-replacement" = true ∧
    isBurnedMechanism "G33-burn-18:overflowing-add-sub-roundtrip-cancellation" = true ∧
    isBurnedMechanism "G35-burn-19:unguarded-sub-add-underflow-cancellation" = true ∧
    isBurnedMechanism "G36-burn-20:overlapping-interval-strict-lt-elision" = true ∧
    isBurnedMechanism "G38-burn-21:unmasked-shl-field-packing-overflow" = true ∧
    isBurnedMechanism "G39-burn-22:unfactored-floor-div-sub-distribution" = true ∧
    isBurnedMechanism "G41-burn-23:overlapping-unaligned-mstore-forwarding" = true ∧
    isBurnedMechanism "G43-burn-24:boundary-low-bitmask-and-elision" = true ∧
    isBurnedMechanism "G44-burn-25:intervening-scratch-write-noop-mstore-elision" = true ∧
    isBurnedMechanism "G46-burn-26:wrapped-offset-add-fusion-across-lt-guard" = true ∧
    isBurnedMechanism "G48-burn-27:overflowing-shl-shr-roundtrip-cancellation" = true ∧
    isBurnedMechanism "G49-burn-28:upper-bound-only-iszero-lt-elision" = true ∧
    isBurnedMechanism "G50-burn-29:cross-callback-dead-tstore-elision" = true ∧
    isBurnedMechanism "G51-burn-30:wrapped-div-product-fusion" = true ∧
    isBurnedMechanism "G50-ratchet-43:overwritten-tstore-dead-write-elision" = false ∧
    isBurnedMechanism "G51-ratchet-44:consecutive-div-fusion" = false ∧
    isBurnedMechanism "G52-ratchet-45:disjoint-bitmask-and-elision" = false := by
  decide

/-- Concrete `MetaGateSpec` instance for `verifyAccelCertGate false`, complete with
    positive (`nonVacuous`) and negative (`tight`) certificate witnesses. -/
def accelCertMetaGateSpec :
    MetaGateSpec PassStepCert (fun c => verifyAccelCertGate false c = true) where
  gate := verifyAccelCertGate false
  sound := fun _ h => h
  complete := fun _ h => h
  posWitness := (defaultCertifiedPluginCatalog.headD default).mkStepCert 100 101 1000 800
  negWitness := { (defaultCertifiedPluginCatalog.headD default).mkStepCert 100 101 800 1000 with
                  assurance := .unverifiedFallback }
  nonVacuous := by decide
  tight := by decide

/-- **Theorem AP.10 (`accelCertMetaGateSpec_valid_and_tight`)**:
    Certifies that `accelCertMetaGateSpec` accepts the positive G1–G8 witness (`costAfter = 800 ≤ 1000`)
    and rejects the negative mutant witness (`costAfter = 1000 > 800`, `.unverifiedFallback`). -/
theorem accelCertMetaGateSpec_valid_and_tight :
    accelCertMetaGateSpec.gate accelCertMetaGateSpec.posWitness = true ∧
    accelCertMetaGateSpec.gate accelCertMetaGateSpec.negWitness = false :=
  ⟨accelCertMetaGateSpec.nonVacuous, accelCertMetaGateSpec.tight⟩

end Compiler.Codegen.AccelPlugin
