/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Verity.Specs.ObsAlgebra

set_option autoImplicit false

namespace Compiler.Autoresearch.SolcBugHunter

open Verity.Specs.ObsAlgebra

/-!
# 4-Way Differential Equivalence Harness & `solc` Compiler Bug Discovery Engine
## Verity 2.0 Unified Roadmap — Part 2.1, 2.2 & 2.4 (Branch `V5-8`)

This module formalizes the 4-way differential execution oracle and automated
`solc` bug-triage algebra described in Part 2 of the unified roadmap:

1. **The 4 Execution Lanes (`FourWayExecutionTrace`)**:
   - **Lane A (`obsSolc`)**: `solc` compiled EVM bytecode executed on `revm`/Foundry,
   - **Lane B (`obsVerityEvm`)**: Verity-compiled Yul/EVM executed on `revm`/Foundry,
   - **Lane C (`obsEvmYulLean`)**: `EvmYulLean 2.0` executable Yul/EVM reference semantics,
   - **Lane D (`obsVerityDenote`)**: Verity Layer 1/2 executable specification (`Denote` / `IRInterpreter`).

2. **Exhaustive 4-Way Triage Decision Algebra (`TriageVerdict`)**:
   - `allFourAgree`: `A = B ∧ B = C ∧ C = D` (full 4-way conformance + gas comparison),
   - `candidateSolcBug`: `(B = C ∧ C = D) ∧ A ≠ B` — the three independent formal/verified
     semantics (`Verity EVM`, `EvmYulLean 2.0`, and `Verity Denote`) agree with each other,
     while `solc` diverges!
   - `verityCodegenBug`: `(A = C ∧ C = D) ∧ B ≠ C` — `Verity` Layer 3/4 codegen diverged,
   - `frontendImportDiscrepancy`: `(A = B ∧ B = C) ∧ D ≠ C` — `SolidityImport` frontend mismatch,
   - `multiWayDivergence`: any other split requiring manual inspection.

3. **Multi-Profile `solc` Pass Localization (`SolcProfileMatrix`)**:
   When `candidateSolcBug` fires, re-running Lane A across:
   - `solc --no-optimize` (`obsLegacyNoOpt`),
   - `solc --optimize` (`obsLegacyOpt`),
   - `solc --via-ir --no-optimize` (`obsViaIrNoOpt`),
   - `solc --via-ir --optimize` (`obsViaIrOpt`)
   pinpoints the exact broken `solc` subsystem (`YulOptimizerBug`, `ViaIrCodegenBug`,
   `LegacyPeepholeBug`, or `FrontendSemanticBug`).
-/

/-! ## 1. 4-Way Differential Execution Trace & Triage Classification -/

/-- Canonical 4-lane observation tuple for a single transaction or multi-tx trace step. -/
structure FourWayTraceStep where
  txLabel : String
  obsSolc : Obs
  obsVerityEvm : Obs
  obsEvmYulLean : Obs
  obsVerityDenote : Obs
  gasSolc : Nat := 0
  gasVerityEvm : Nat := 0
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Classification of a `FourWayTraceStep` across the four execution lanes. -/
inductive TriageVerdict where
  | allFourAgree
  | candidateSolcBug
  | verityCodegenBug
  | frontendImportDiscrepancy
  | multiWayDivergence
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Deterministic classifier mapping any `FourWayTraceStep` to its `TriageVerdict`. -/
def classifyFourWayStep (step : FourWayTraceStep) : TriageVerdict :=
  let bEqC := obsEquivBool step.obsVerityEvm step.obsEvmYulLean
  let cEqD := obsEquivBool step.obsEvmYulLean step.obsVerityDenote
  let aEqB := obsEquivBool step.obsSolc step.obsVerityEvm
  let aEqC := obsEquivBool step.obsSolc step.obsEvmYulLean
  if aEqB && bEqC && cEqD then
    .allFourAgree
  else if bEqC && cEqD && !aEqB then
    .candidateSolcBug
  else if aEqC && cEqD && !bEqC then
    .verityCodegenBug
  else if aEqB && bEqC && !cEqD then
    .frontendImportDiscrepancy
  else
    .multiWayDivergence

/-- **Theorem 2.2.1 (`allFourAgree` Exact Characterization)**:
    `classifyFourWayStep step = .allFourAgree` holds if and only if all four lanes
    produce identical canonical `Obs` records (`A = B = C = D`). -/
theorem classifyFourWayStep_allFourAgree_iff (step : FourWayTraceStep) :
    classifyFourWayStep step = .allFourAgree ↔
      (step.obsSolc = step.obsVerityEvm ∧
       step.obsVerityEvm = step.obsEvmYulLean ∧
       step.obsEvmYulLean = step.obsVerityDenote) := by
  unfold classifyFourWayStep obsEquivBool
  by_cases hab : step.obsSolc = step.obsVerityEvm <;>
  by_cases hbc : step.obsVerityEvm = step.obsEvmYulLean <;>
  by_cases hcd : step.obsEvmYulLean = step.obsVerityDenote <;>
  by_cases hac : step.obsSolc = step.obsEvmYulLean <;>
  simp_all

/-- **Theorem 2.2.2 (`candidateSolcBug` Soundness)**:
    Whenever `classifyFourWayStep step = .candidateSolcBug`, the three formal lanes
    (`obsVerityEvm`, `obsEvmYulLean`, `obsVerityDenote`) are mutually equal (`B = C = D`),
    and `obsSolc` strictly disagrees with them (`A ≠ B`). -/
theorem classifyFourWayStep_candidateSolcBug_sound (step : FourWayTraceStep)
    (hbug : classifyFourWayStep step = .candidateSolcBug) :
    step.obsVerityEvm = step.obsEvmYulLean ∧
    step.obsEvmYulLean = step.obsVerityDenote ∧
    step.obsSolc ≠ step.obsVerityEvm := by
  unfold classifyFourWayStep obsEquivBool at hbug
  by_cases hab : step.obsSolc = step.obsVerityEvm <;>
  by_cases hbc : step.obsVerityEvm = step.obsEvmYulLean <;>
  by_cases hcd : step.obsEvmYulLean = step.obsVerityDenote <;>
  by_cases hac : step.obsSolc = step.obsEvmYulLean <;>
  simp_all

/-! ## 2. Multi-Profile `solc` Optimizer Bug Localization (Part 2.4) -/

/-- Fine-grained `solc` compiler bug category isolated by comparing `--no-optimize`,
    `--optimize`, `--via-ir --no-optimize`, and `--via-ir --optimize` against the
    verified reference observation `obsRef`. -/
inductive SolcBugSubsystem where
  | noBug
  | yulOptimizerStepBug
  | viaIrLoweringBug
  | legacyPeepholeOptimizerBug
  | frontendSemanticBug
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Multi-profile `solc` execution matrix for a single input trace. -/
structure SolcProfileMatrix where
  obsRef : Obs
  obsLegacyNoOpt : Obs
  obsLegacyOpt : Obs
  obsViaIrNoOpt : Obs
  obsViaIrOpt : Obs
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Pinpoint which `solc` compiler pass introduced the divergence from `obsRef`:
    - If `--via-ir --no-optimize` matches `obsRef` (`= B = C = D`) but `--via-ir --optimize`
      diverges, the bug is inside `solc`'s Yul optimizer (`yulOptimizerStepBug`: e.g.
      `FullInliner`, `ExpressionSimplifier`, `LoadResolver`, `UnusedPruner`).
    - If `--no-optimize` matches `obsRef` but `--via-ir --no-optimize` diverges, the bug is
      in `solc`'s Solidity-to-Yul IR codegen (`viaIrLoweringBug`).
    - If `--no-optimize` matches `obsRef` but `--optimize` (legacy pipeline) diverges, the
      bug is in `solc`'s legacy bytecode peephole/deduplicator (`legacyPeepholeOptimizerBug`).
    - If even `--no-optimize` diverges from `obsRef`, it is a `frontendSemanticBug`. -/
def localizeSolcBugSubsystem (m : SolcProfileMatrix) : SolcBugSubsystem :=
  let legNoOptOk := obsEquivBool m.obsLegacyNoOpt m.obsRef
  let legOptOk := obsEquivBool m.obsLegacyOpt m.obsRef
  let irNoOptOk := obsEquivBool m.obsViaIrNoOpt m.obsRef
  let irOptOk := obsEquivBool m.obsViaIrOpt m.obsRef
  if legNoOptOk && legOptOk && irNoOptOk && irOptOk then
    .noBug
  else if irNoOptOk && !irOptOk then
    .yulOptimizerStepBug
  else if legNoOptOk && !irNoOptOk then
    .viaIrLoweringBug
  else if legNoOptOk && !legOptOk then
    .legacyPeepholeOptimizerBug
  else
    .frontendSemanticBug

/-- **Theorem 2.4.1 (Yul Optimizer Bug Pinpointing)**:
    Whenever `localizeSolcBugSubsystem m = .yulOptimizerStepBug`, `solc --via-ir --no-optimize`
    agrees with the verified reference `obsRef` while `solc --via-ir --optimize` diverges,
    proving that `solc`'s Yul optimizer introduced the semantic corruption. -/
theorem localizeSolcBug_yulOptimizer_sound (m : SolcProfileMatrix)
    (hyul : localizeSolcBugSubsystem m = .yulOptimizerStepBug) :
    m.obsViaIrNoOpt = m.obsRef ∧ m.obsViaIrOpt ≠ m.obsRef := by
  unfold localizeSolcBugSubsystem obsEquivBool at hyul
  by_cases h1 : m.obsLegacyNoOpt = m.obsRef <;>
  by_cases h2 : m.obsLegacyOpt = m.obsRef <;>
  by_cases h3 : m.obsViaIrNoOpt = m.obsRef <;>
  by_cases h4 : m.obsViaIrOpt = m.obsRef <;>
  simp_all

/-- **Executable Witness Suite (`by decide`, `0 native_decide`)**:
    Demonstrates automated detection of a `solc --via-ir --optimize` `LoadResolver`
    stale-cache bug where `B = C = D` return storage `[(0, 99)]` while `solc --via-ir --optimize`
    returns stale storage `[(0, 1)]`. -/
theorem solcBugHunter_executable_witness :
    let refObs : Obs := { status := .success, returndata := [99], logs := [], storage := [(0, 99)], transient := [] }
    let buggySolcObs : Obs := { status := .success, returndata := [1], logs := [], storage := [(0, 1)], transient := [] }
    let step : FourWayTraceStep :=
      { txLabel := "swap_dirty_transient_tstore_sload"
        obsSolc := buggySolcObs
        obsVerityEvm := refObs
        obsEvmYulLean := refObs
        obsVerityDenote := refObs
        gasSolc := 42100
        gasVerityEvm := 41083 }
    let matrix : SolcProfileMatrix :=
      { obsRef := refObs
        obsLegacyNoOpt := refObs
        obsLegacyOpt := refObs
        obsViaIrNoOpt := refObs
        obsViaIrOpt := buggySolcObs }
    classifyFourWayStep step = .candidateSolcBug ∧
    localizeSolcBugSubsystem matrix = .yulOptimizerStepBug := by
  decide

end Compiler.Autoresearch.SolcBugHunter
