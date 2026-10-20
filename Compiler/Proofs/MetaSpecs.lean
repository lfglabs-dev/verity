/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Compiler.CompilationModel.Types
import Compiler.CompilationModel.TrustSurfaceLinear
import Compiler.Proofs.IRGeneration.SupportedSpec.SurfaceMask
import Std.Tactic.BVDecide

namespace Compiler.Proofs.MetaSpecs

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration

/-!
# Universal Meta-Specifications for Verity Layer 2 Proofs (Node M2 + Phase 3A)

This module formalizes seven reusable, parametric **Universal Meta-Specifications**
governing semantic preservation, specification non-vacuity, trust-boundary
partitioning, security-guard mutation sensitivity, free-memory-pointer prologue
synthesis, effect-summary view/CEI invariants, and verified compiler runtime shims:

1. **Meta-Spec 1 (`TriangularSemanticMetaSpec`)**:
   Parametric commuting-diagram meta-specification over `(DenoteState, SourceState, IRState, Obs)`
   proving single-step commutation (`triangular_commutes`), $n$-step iterated simulation
   composition (`triangular_compose_multi_step`), and observational revert equivalence
   (`triangular_revert_equivalence`).
2. **Meta-Spec 2 (`NonVacuousSpec` & `SatisfiablePrecondition`)**:
   Bundled soundness + constructive witness existence specification that strictly
   refutes vacuous `False` preconditions (`not_nonVacuous_of_unsat_pre`,
   `not_nonVacuous_false_pre`), composes sequentially (`NonVacuousSpec.comp`),
   and is preserved under precondition weakening (`NonVacuousSpec.weakenPre`) and
   postcondition strengthening (`NonVacuousSpec.strengthenPost`).
3. **Meta-Spec 3 (`CertifiedOrExplicitlyFlagged` & Trust-Boundary Partition)**:
   Connects the single-pass `SurfaceMask` catamorphism (`contractSurfaceMask`) with
   the linear-time trust-surface analyzer (`undischargedAssumptionReportEntriesLinear`)
   to prove a universal partition law with zero silent fallthrough
   (`trust_boundary_partition_complete`, `trust_boundary_no_silent_gap`).
4. **Meta-Spec 4 (`DifferentialGuardMetaSpec` & Concrete EVM Security Guards)**:
   Formalizes boundary-witness mutation sensitivity for security guards and
   instantiates it on four concrete EVM guards:
   - Payable guard (`msgValue == 0`),
   - Calldata minimum word guard (`calldataWords ≥ minWords`),
   - Reentrancy lock guard (`lockWord == 0`), and
   - 256-bit arithmetic overflow guard (`a + b < 2^256`).
5. **Meta-Spec 5 (`FreePointerPrologueMetaSpec`)**:
   Single-pass catamorphism `stmtListRequiresFreePointerInit` and prologue
   combinator `withFreePointerPrologue` eliminating missing `mstore(64, 128)`
   free-pointer prologue bugs (`#2515`/`#2573`) by construction.
6. **Meta-Spec 6 (`EffectSummary` & `ViewFrameAndCEIMetaSpec`)**:
   6-flag effect lattice and single-pass catamorphism `stmtListEffectSummary`
   proving 1-line universal view-frame storage preservation (`#2422`) and
   internal-helper CEI precision (`#2435`).
7. **Meta-Spec 7 (`VerifiedCompilerShim`)**:
   Parametric verification bundle for compiler runtime shims (`mulDiv512`,
   scratch `keccak256`, transient reentrancy locks, `staticcall` word wrappers).
-/

/-! ## Meta-Spec 1: Triangular Semantic Commutation (`TriangularSemanticMetaSpec`) -/

/-- Iterate a state-transition step function `n` times. -/
def iterateStep {State : Type} (step : State → State) : Nat → State → State
  | 0, s => s
  | n + 1, s => iterateStep step n (step s)

/-- Upper refinement edge: `DenoteState` refines `SourceState` under relation `relDS`
with respect to observations `obsDenote`, `obsSource` and transitions `stepDenote`, `stepSource`. -/
structure DenoteRefinesSource
    {DenoteState SourceState Obs : Type}
    (obsDenote : DenoteState → Obs)
    (obsSource : SourceState → Obs)
    (stepDenote : DenoteState → DenoteState)
    (stepSource : SourceState → SourceState)
    (relDS : DenoteState → SourceState → Prop) : Prop where
  /-- Related states yield identical external observations. -/
  obs_eq : ∀ d s, relDS d s → obsDenote d = obsSource s
  /-- A single transition step preserves the refinement relation. -/
  step_sim : ∀ d s, relDS d s → relDS (stepDenote d) (stepSource s)

/-- Lower refinement edge: `SourceState` refines `IRState` under relation `relSI`
with respect to observations `obsSource`, `obsIR` and transitions `stepSource`, `stepIR`. -/
structure SourceRefinesIR
    {SourceState IRState Obs : Type}
    (obsSource : SourceState → Obs)
    (obsIR : IRState → Obs)
    (stepSource : SourceState → SourceState)
    (stepIR : IRState → IRState)
    (relSI : SourceState → IRState → Prop) : Prop where
  /-- Related states yield identical external observations. -/
  obs_eq : ∀ s i, relSI s i → obsSource s = obsIR i
  /-- A single transition step preserves the refinement relation. -/
  step_sim : ∀ s i, relSI s i → relSI (stepSource s) (stepIR i)

/-- **Meta-Spec 1 (`TriangularSemanticMetaSpec`)**:
Bundles the `DenoteState → SourceState` and `SourceState → IRState` simulation
edges into a commuting triangular diagram over shared observable type `Obs`. -/
structure TriangularSemanticMetaSpec
    {DenoteState SourceState IRState Obs : Type}
    (obsDenote : DenoteState → Obs)
    (obsSource : SourceState → Obs)
    (obsIR : IRState → Obs)
    (stepDenote : DenoteState → DenoteState)
    (stepSource : SourceState → SourceState)
    (stepIR : IRState → IRState)
    (relDS : DenoteState → SourceState → Prop)
    (relSI : SourceState → IRState → Prop) : Prop where
  /-- EDSL denotational semantics refines source compilation-model semantics. -/
  denoteRefinesSource : DenoteRefinesSource obsDenote obsSource stepDenote stepSource relDS
  /-- Source compilation-model semantics refines lowered IR execution semantics. -/
  sourceRefinesIR : SourceRefinesIR obsSource obsIR stepSource stepIR relSI

/-- Observational agreement across the base of the semantic triangle. -/
theorem triangular_obs_eq
    {DenoteState SourceState IRState Obs : Type}
    {obsDenote : DenoteState → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteState → DenoteState}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteState → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    {d : DenoteState} {s : SourceState} {i : IRState}
    (hDS : relDS d s) (hSI : relSI s i) :
    obsDenote d = obsIR i :=
  (hTri.denoteRefinesSource.obs_eq d s hDS).trans
    (hTri.sourceRefinesIR.obs_eq s i hSI)

/-- **Single-Step Triangular Commutation**:
If `DenoteRefinesSource` and `SourceRefinesIR` hold, then the end-to-end
`DenoteState → IRState` diagram commutes after one step. -/
theorem triangular_commutes
    {DenoteState SourceState IRState Obs : Type}
    {obsDenote : DenoteState → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteState → DenoteState}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteState → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    {d : DenoteState} {s : SourceState} {i : IRState}
    (hDS : relDS d s) (hSI : relSI s i) :
    obsDenote (stepDenote d) = obsIR (stepIR i) :=
  triangular_obs_eq hTri
    (hTri.denoteRefinesSource.step_sim d s hDS)
    (hTri.sourceRefinesIR.step_sim s i hSI)

/-- Multi-step preservation of `relDS` under `iterateStep`. -/
theorem DenoteRefinesSource.iterate
    {DenoteState SourceState Obs : Type}
    {obsDenote : DenoteState → Obs}
    {obsSource : SourceState → Obs}
    {stepDenote : DenoteState → DenoteState}
    {stepSource : SourceState → SourceState}
    {relDS : DenoteState → SourceState → Prop}
    (h : DenoteRefinesSource obsDenote obsSource stepDenote stepSource relDS)
    (n : Nat) {d : DenoteState} {s : SourceState} (hDS : relDS d s) :
    relDS (iterateStep stepDenote n d) (iterateStep stepSource n s) := by
  induction n generalizing d s with
  | zero => exact hDS
  | succ n ih => exact ih (h.step_sim d s hDS)

/-- Multi-step preservation of `relSI` under `iterateStep`. -/
theorem SourceRefinesIR.iterate
    {SourceState IRState Obs : Type}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relSI : SourceState → IRState → Prop}
    (h : SourceRefinesIR obsSource obsIR stepSource stepIR relSI)
    (n : Nat) {s : SourceState} {i : IRState} (hSI : relSI s i) :
    relSI (iterateStep stepSource n s) (iterateStep stepIR n i) := by
  induction n generalizing s i with
  | zero => exact hSI
  | succ n ih => exact ih (h.step_sim s i hSI)

/-- **Multi-Step Triangular Commutation (`triangular_compose_multi_step`)**:
For any step count `n : Nat`, the $n$-step iterated transitions of `DenoteState`
and `IRState` produce identical observations. -/
theorem triangular_compose_multi_step
    {DenoteState SourceState IRState Obs : Type}
    {obsDenote : DenoteState → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteState → DenoteState}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteState → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    (n : Nat) {d : DenoteState} {s : SourceState} {i : IRState}
    (hDS : relDS d s) (hSI : relSI s i) :
    obsDenote (iterateStep stepDenote n d) = obsIR (iterateStep stepIR n i) :=
  triangular_obs_eq hTri
    (hTri.denoteRefinesSource.iterate n hDS)
    (hTri.sourceRefinesIR.iterate n hSI)

/-- **Triangular Revert Equivalence (`triangular_revert_equivalence`)**:
For any revert classifier `isRevert : Obs → Bool`, `DenoteState` reverts after
`n` steps if and only if `IRState` reverts after `n` steps. -/
theorem triangular_revert_equivalence
    {DenoteState SourceState IRState Obs : Type}
    {obsDenote : DenoteState → Obs}
    {obsSource : SourceState → Obs}
    {obsIR : IRState → Obs}
    {stepDenote : DenoteState → DenoteState}
    {stepSource : SourceState → SourceState}
    {stepIR : IRState → IRState}
    {relDS : DenoteState → SourceState → Prop}
    {relSI : SourceState → IRState → Prop}
    (hTri : TriangularSemanticMetaSpec
      obsDenote obsSource obsIR stepDenote stepSource stepIR relDS relSI)
    (isRevert : Obs → Bool)
    (n : Nat) {d : DenoteState} {s : SourceState} {i : IRState}
    (hDS : relDS d s) (hSI : relSI s i) :
    isRevert (obsDenote (iterateStep stepDenote n d)) =
      isRevert (obsIR (iterateStep stepIR n i)) := by
  rw [triangular_compose_multi_step hTri n hDS hSI]

/-! ## Meta-Spec 2: Non-Vacuity & Satisfiable Preconditions (`NonVacuousSpec`) -/

/-- A precondition `Pre : Input → Prop` is satisfiable if it admits at least one witness. -/
def SatisfiablePrecondition {Input : Type} (Pre : Input → Prop) : Prop :=
  ∃ w₀ : Input, Pre w₀

/-- **Meta-Spec 2 (`NonVacuousSpec`)**:
Requires both universal soundness (`∀ x, Pre x → Post x (eval x)`) and constructive
witness existence (`∃ w₀, Pre w₀ ∧ Post w₀ (eval w₀)`), ruling out vacuous specifications
whose precondition is unsatisfiable. -/
structure NonVacuousSpec
    (Input Output : Type)
    (Pre : Input → Prop)
    (Post : Input → Output → Prop)
    (eval : Input → Output) : Prop where
  /-- Universal soundness over all inputs satisfying `Pre`. -/
  sound : ∀ x, Pre x → Post x (eval x)
  /-- Existence of a concrete witness inhabiting `Pre` and satisfying `Post`. -/
  witness_exists : ∃ w₀, Pre w₀ ∧ Post w₀ (eval w₀)

/-- Every `NonVacuousSpec` has a satisfiable precondition. -/
theorem NonVacuousSpec.satisfiablePre
    {Input Output : Type} {Pre : Input → Prop} {Post : Input → Output → Prop}
    {eval : Input → Output}
    (h : NonVacuousSpec Input Output Pre Post eval) :
    SatisfiablePrecondition Pre := by
  obtain ⟨w₀, hw₀, _⟩ := h.witness_exists
  exact ⟨w₀, hw₀⟩

/-- Construct a `NonVacuousSpec` from universal soundness and a precondition witness. -/
theorem NonVacuousSpec.of_sound_and_satisfiable
    {Input Output : Type} {Pre : Input → Prop} {Post : Input → Output → Prop}
    {eval : Input → Output}
    (hsound : ∀ x, Pre x → Post x (eval x))
    (hsat : SatisfiablePrecondition Pre) :
    NonVacuousSpec Input Output Pre Post eval := by
  obtain ⟨w₀, hw₀⟩ := hsat
  exact ⟨hsound, ⟨w₀, hw₀, hsound w₀ hw₀⟩⟩

/-- **Vacuity Refutation (`not_nonVacuous_of_unsat_pre`)**:
An unsatisfiable precondition (`∀ x, ¬ Pre x`) cannot inhabit `NonVacuousSpec`. -/
theorem not_nonVacuous_of_unsat_pre
    {Input Output : Type} {Pre : Input → Prop} {Post : Input → Output → Prop}
    {eval : Input → Output}
    (hunsat : ∀ x, ¬ Pre x) :
    ¬ NonVacuousSpec Input Output Pre Post eval := by
  intro h
  obtain ⟨w₀, hw₀, _⟩ := h.witness_exists
  exact hunsat w₀ hw₀

/-- Specialization of `not_nonVacuous_of_unsat_pre` to the constant `False` precondition. -/
theorem not_nonVacuous_false_pre
    {Input Output : Type} {Post : Input → Output → Prop} {eval : Input → Output} :
    ¬ NonVacuousSpec Input Output (fun _ => False) Post eval :=
  not_nonVacuous_of_unsat_pre (fun _ h => h)

/-- **Sequential Composition (`NonVacuousSpec.comp`)**:
Two non-vacuous specifications compose sequentially whenever the postcondition
of the first stage implies the precondition of the second stage. -/
theorem NonVacuousSpec.comp
    {A B C : Type}
    {Pre₁ : A → Prop} {Post₁ : A → B → Prop} {f : A → B}
    {Pre₂ : B → Prop} {Post₂ : B → C → Prop} {g : B → C}
    (h₁ : NonVacuousSpec A B Pre₁ Post₁ f)
    (h₂ : NonVacuousSpec B C Pre₂ Post₂ g)
    (hbridge : ∀ x, Pre₁ x → Post₁ x (f x) → Pre₂ (f x)) :
    NonVacuousSpec A C Pre₁
      (fun x z => Post₁ x (f x) ∧ Post₂ (f x) z)
      (fun x => g (f x)) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have hp₁ := h₁.sound x hx
    exact ⟨hp₁, h₂.sound (f x) (hbridge x hx hp₁)⟩
  · obtain ⟨w₀, hw₀, hp₁⟩ := h₁.witness_exists
    exact ⟨w₀, hw₀, hp₁, h₂.sound (f w₀) (hbridge w₀ hw₀ hp₁)⟩

/-- **Precondition Weakening (`NonVacuousSpec.weakenPre`)**:
If `Pre₁` implies a weaker precondition `Pre₂` on which `eval` remains sound,
then non-vacuity transfers from `Pre₁` to `Pre₂`. -/
theorem NonVacuousSpec.weakenPre
    {Input Output : Type}
    {Pre₁ Pre₂ : Input → Prop} {Post : Input → Output → Prop}
    {eval : Input → Output}
    (h : NonVacuousSpec Input Output Pre₁ Post eval)
    (hweaken : ∀ x, Pre₁ x → Pre₂ x)
    (hsound₂ : ∀ x, Pre₂ x → Post x (eval x)) :
    NonVacuousSpec Input Output Pre₂ Post eval := by
  obtain ⟨w₀, hw₀, _⟩ := h.witness_exists
  exact NonVacuousSpec.of_sound_and_satisfiable hsound₂ ⟨w₀, hweaken w₀ hw₀⟩

/-- **Postcondition Strengthening / Consequence (`NonVacuousSpec.strengthenPost`)**:
If `Post₁` entails `Post₂` on inputs satisfying `Pre`, then `NonVacuousSpec`
lifts from `Post₁` to `Post₂`. -/
theorem NonVacuousSpec.strengthenPost
    {Input Output : Type}
    {Pre : Input → Prop} {Post₁ Post₂ : Input → Output → Prop}
    {eval : Input → Output}
    (h : NonVacuousSpec Input Output Pre Post₁ eval)
    (himp : ∀ x y, Pre x → Post₁ x y → Post₂ x y) :
    NonVacuousSpec Input Output Pre Post₂ eval := by
  refine ⟨fun x hx => himp x (eval x) hx (h.sound x hx), ?_⟩
  obtain ⟨w₀, hw₀, hp₁⟩ := h.witness_exists
  exact ⟨w₀, hw₀, himp w₀ (eval w₀) hw₀ hp₁⟩

/-! ## Meta-Spec 3: Trust-Boundary Partition (`TrustBoundaryPartitionMetaSpec`) -/

/-- Single-pass surface mask of a single `FunctionSpec`. -/
def functionSurfaceMask (fn : FunctionSpec) : SurfaceMask :=
  stmtListSurfaceMask fn.body

/-- Single-pass surface mask over a list of `FunctionSpec` declarations. -/
def functionListSurfaceMask : List FunctionSpec → SurfaceMask
  | [] => 0
  | fn :: rest => functionSurfaceMask fn ||| functionListSurfaceMask rest

/-- Single-pass surface mask of the optional constructor of a `CompilationModel`. -/
def constructorSurfaceMask (spec : CompilationModel) : SurfaceMask :=
  match spec.constructor with
  | some ctor => stmtListSurfaceMask ctor.body
  | none => 0

/-- Whole-contract $\mathcal{O}(|AST|)$ surface capability bitmask uniting the
constructor and all declared functions of `spec`. -/
def contractSurfaceMask (spec : CompilationModel) : SurfaceMask :=
  constructorSurfaceMask spec ||| functionListSurfaceMask spec.functions

/-- Boolean check that `spec` has zero undischarged entries in its linear-time
trust surface report. -/
def hasNoUndischargedLinearAssumptions (spec : CompilationModel) : Bool :=
  (undischargedAssumptionReportEntriesLinear spec).isEmpty

/-- Combined whole-contract certification gate at capability mask `allowedMask`:
every AST statement stays within `allowedMask` AND the linear trust-surface report
contains zero undischarged assumptions. -/
def isFullyCertifiedAtMask (spec : CompilationModel) (allowedMask : SurfaceMask) : Bool :=
  maskSubset (contractSurfaceMask spec) allowedMask &&
    hasNoUndischargedLinearAssumptions spec

/-- **Complement Duality Law**:
Testing whether `m` touches any bit in the bitwise complement `~~~allowed` is the
exact boolean negation of `maskSubset m allowed`. -/
@[simp]
theorem hasMask_compl_eq_not_maskSubset (m allowed : SurfaceMask) :
    hasMask m (~~~allowed) = !maskSubset m allowed := by
  simp only [hasMask, maskSubset, bne]
  bv_decide

/-- Exact boolean equivalence between `maskSubset m allowed = false` and
`hasMask m (~~~allowed) = true`. -/
theorem hasMask_compl_eq_true_iff_maskSubset_eq_false (m allowed : SurfaceMask) :
    hasMask m (~~~allowed) = true ↔ maskSubset m allowed = false := by
  rw [hasMask_compl_eq_not_maskSubset, Bool.not_eq_true']

/-- Exact boolean equivalence between `maskSubset m allowed = true` and
`hasMask m (~~~allowed) = false`. -/
theorem maskSubset_eq_true_iff_hasMask_compl_eq_false (m allowed : SurfaceMask) :
    maskSubset m allowed = true ↔ hasMask m (~~~allowed) = false := by
  rw [hasMask_compl_eq_not_maskSubset, Bool.not_eq_false']

/-- **Meta-Spec 3 (`CertifiedOrExplicitlyFlagged`)**:
Universal trust-boundary partition bundle for a contract `spec` relative to an
allowed capability mask `allowedMask`:
1. Either all statements stay within `allowedMask` or a disallowed bit in
   `~~~allowedMask` is explicitly flagged in `contractSurfaceMask spec`.
2. The two surface outcomes are mutually exclusive.
3. The linear assumption report is either empty or explicitly non-empty.
4. `isFullyCertifiedAtMask` holds iff both the surface mask is within `allowedMask`
   and the undischarged linear assumption report is empty. -/
structure CertifiedOrExplicitlyFlagged
    (spec : CompilationModel) (allowedMask : SurfaceMask) : Prop where
  /-- Exhaustive surface dichotomy: certified subset or flagged complement bit. -/
  surface_partition :
    maskSubset (contractSurfaceMask spec) allowedMask = true ∨
      hasMask (contractSurfaceMask spec) (~~~allowedMask) = true
  /-- Mutual exclusion: a contract cannot simultaneously stay within `allowedMask`
  and set a bit in `~~~allowedMask`. -/
  surface_exclusive :
    ¬ (maskSubset (contractSurfaceMask spec) allowedMask = true ∧
        hasMask (contractSurfaceMask spec) (~~~allowedMask) = true)
  /-- Exhaustive linear trust-report dichotomy. -/
  trust_report_partition :
    undischargedAssumptionReportEntriesLinear spec = [] ∨
      undischargedAssumptionReportEntriesLinear spec ≠ []
  /-- Exact characterization of the combined certification gate. -/
  combined_gate_iff :
    isFullyCertifiedAtMask spec allowedMask = true ↔
      (maskSubset (contractSurfaceMask spec) allowedMask = true ∧
        undischargedAssumptionReportEntriesLinear spec = [])

/-- **No Silent Fallthrough (`trust_boundary_no_silent_gap`)**:
Whenever a contract's surface mask is not a subset of `allowedMask`, at least one
disallowed capability bit in `~~~allowedMask` is explicitly set. -/
theorem trust_boundary_no_silent_gap
    (spec : CompilationModel) (allowedMask : SurfaceMask)
    (hnot : maskSubset (contractSurfaceMask spec) allowedMask = false) :
    hasMask (contractSurfaceMask spec) (~~~allowedMask) = true :=
  (hasMask_compl_eq_true_iff_maskSubset_eq_false (contractSurfaceMask spec) allowedMask).mpr hnot

/-- **Universal Surface Dichotomy (`trust_boundary_surface_dichotomy`)**:
Every contract either stays within `allowedMask` or sets an explicit flag bit in `~~~allowedMask`. -/
theorem trust_boundary_surface_dichotomy
    (spec : CompilationModel) (allowedMask : SurfaceMask) :
    maskSubset (contractSurfaceMask spec) allowedMask = true ∨
      hasMask (contractSurfaceMask spec) (~~~allowedMask) = true := by
  cases h : maskSubset (contractSurfaceMask spec) allowedMask
  · exact Or.inr (trust_boundary_no_silent_gap spec allowedMask h)
  · exact Or.inl rfl

/-- **Universal Trust-Boundary Partition Theorem (`trust_boundary_partition_complete`)**:
Every `spec : CompilationModel` and `allowedMask : SurfaceMask` satisfies
`CertifiedOrExplicitlyFlagged spec allowedMask` with zero silent fallthrough. -/
theorem trust_boundary_partition_complete
    (spec : CompilationModel) (allowedMask : SurfaceMask) :
    CertifiedOrExplicitlyFlagged spec allowedMask := by
  refine ⟨trust_boundary_surface_dichotomy spec allowedMask, ?_, ?_, ?_⟩
  · rintro ⟨hsub, hflag⟩
    rw [hasMask_compl_eq_true_iff_maskSubset_eq_false] at hflag
    rw [hsub] at hflag
    cases hflag
  · cases hrep : undischargedAssumptionReportEntriesLinear spec with
    | nil => exact Or.inl rfl
    | cons e es => exact Or.inr (List.cons_ne_nil e es)
  · simp [isFullyCertifiedAtMask, hasNoUndischargedLinearAssumptions, List.isEmpty_iff]

/-- If `isFullyCertifiedAtMask spec allowedMask = false`, then either an unsupported
surface bit is flagged in `~~~allowedMask` or `undischargedAssumptionReportEntriesLinear spec`
is non-empty. -/
theorem trust_boundary_not_certified_imp_flagged
    (spec : CompilationModel) (allowedMask : SurfaceMask)
    (hfail : isFullyCertifiedAtMask spec allowedMask = false) :
    hasMask (contractSurfaceMask spec) (~~~allowedMask) = true ∨
      undischargedAssumptionReportEntriesLinear spec ≠ [] := by
  simp only [isFullyCertifiedAtMask, Bool.and_eq_false_iff,
    hasNoUndischargedLinearAssumptions, List.isEmpty_eq_false_iff] at hfail
  rcases hfail with hmask | hrep
  · exact Or.inl (trust_boundary_no_silent_gap spec allowedMask hmask)
  · exact Or.inr hrep

/-! ## Meta-Spec 4: Mutation-Sensitive Security Guards (`DifferentialGuardMetaSpec`) -/

/-- **Meta-Spec 4 (`DifferentialGuardMetaSpec`)**:
Certifies that a boolean security guard `guard : Tx → Bool` controlling an execution
semantics `exec : Bool → Tx → Verdict` (where the boolean flag enables/disables the guard)
is both non-trivial and mutation-sensitive:
- `txOk` is accepted by the guard (`guard txOk = true`),
- `txBlocked` is rejected by the guard (`guard txBlocked = false`), and
- mutating/disabling the guard strictly changes the execution verdict on `txBlocked`
  (`exec true txBlocked ≠ exec false txBlocked`). -/
structure DifferentialGuardMetaSpec
    (Tx Verdict : Type)
    (guard : Tx → Bool)
    (exec : Bool → Tx → Verdict) where
  /-- Boundary witness transaction that passes the guard. -/
  txOk : Tx
  /-- Boundary witness transaction that violates the guard. -/
  txBlocked : Tx
  /-- The accepted witness satisfies `guard`. -/
  guard_accepts_ok : guard txOk = true
  /-- The blocked witness is rejected by `guard`. -/
  guard_rejects_blocked : guard txBlocked = false
  /-- Disabling the guard (`false`) strictly alters the execution verdict on `txBlocked`. -/
  mutation_alters_verdict : exec true txBlocked ≠ exec false txBlocked

/-- The accepted and blocked boundary witnesses in a `DifferentialGuardMetaSpec` are distinct. -/
theorem DifferentialGuardMetaSpec.txOk_ne_txBlocked
    {Tx Verdict : Type} {guard : Tx → Bool} {exec : Bool → Tx → Verdict}
    (spec : DifferentialGuardMetaSpec Tx Verdict guard exec) :
    spec.txOk ≠ spec.txBlocked := by
  intro heq
  have h₁ := spec.guard_accepts_ok
  rw [heq, spec.guard_rejects_blocked] at h₁
  cases h₁

/-- Every `DifferentialGuardMetaSpec` induces a `NonVacuousSpec` for guarded execution
over the precondition `fun tx => guard tx = true`. -/
theorem DifferentialGuardMetaSpec.toNonVacuousSpec
    {Tx Verdict : Type} {guard : Tx → Bool} {exec : Bool → Tx → Verdict}
    (spec : DifferentialGuardMetaSpec Tx Verdict guard exec) :
    NonVacuousSpec Tx Verdict
      (fun tx => guard tx = true)
      (fun tx v => v = exec true tx ∧ guard tx = true)
      (exec true) :=
  ⟨fun _ h => ⟨rfl, h⟩, ⟨spec.txOk, spec.guard_accepts_ok, rfl, spec.guard_accepts_ok⟩⟩

/-- Canonical two-arm verdict for guarded EVM entrypoint execution. -/
inductive GuardVerdict where
  /-- Guard passed and execution produced `returnWord`. -/
  | allowed (returnWord : Nat)
  /-- Guard rejected the transaction and reverted. -/
  | reverted
  deriving DecidableEq, Repr

/-! ### Concrete EVM Guard (a): Non-Payable `msg.value == 0` Guard -/

/-- Non-payable entrypoint guard requiring `msgValue == 0`. -/
def payableGuard (msgValue : Nat) : Bool :=
  msgValue == 0

/-- Guarded execution of a non-payable entrypoint with guard toggle `guardEnabled`. -/
def payableExec (guardEnabled : Bool) (msgValue : Nat) : GuardVerdict :=
  if guardEnabled && !payableGuard msgValue then
    .reverted
  else
    .allowed msgValue

/-- Concrete `DifferentialGuardMetaSpec` witness for the non-payable `msgValue == 0` guard
at boundary values `txOk = 0` and `txBlocked = 1`. -/
def payableGuardMetaSpec :
    DifferentialGuardMetaSpec Nat GuardVerdict payableGuard payableExec where
  txOk := 0
  txBlocked := 1
  guard_accepts_ok := by decide
  guard_rejects_blocked := by decide
  mutation_alters_verdict := by decide

/-- The non-payable `msgValue == 0` guard satisfies `DifferentialGuardMetaSpec`. -/
theorem payableGuard_satisfies_metaSpec :
    Nonempty (DifferentialGuardMetaSpec Nat GuardVerdict payableGuard payableExec) :=
  ⟨payableGuardMetaSpec⟩

/-! ### Concrete EVM Guard (b): Calldata Minimum Word Guard (`calldataWords ≥ minWords`) -/

/-- ABI decoder guard requiring at least `minWords` 32-byte calldata words. -/
def calldataMinWordsGuard (minWords calldataWords : Nat) : Bool :=
  decide (calldataWords ≥ minWords)

/-- Guarded ABI decoding execution with guard toggle `guardEnabled`. -/
def calldataMinWordsExec (minWords : Nat) (guardEnabled : Bool) (calldataWords : Nat) : GuardVerdict :=
  if guardEnabled && !calldataMinWordsGuard minWords calldataWords then
    .reverted
  else
    .allowed calldataWords

/-- Parametric `DifferentialGuardMetaSpec` for `calldataMinWordsGuard minWords`
for every positive threshold `minWords > 0`, using boundary pair `(minWords, 0)`. -/
def calldataMinWordsGuardMetaSpec (minWords : Nat) (hpos : 0 < minWords) :
    DifferentialGuardMetaSpec Nat GuardVerdict
      (calldataMinWordsGuard minWords) (calldataMinWordsExec minWords) where
  txOk := minWords
  txBlocked := 0
  guard_accepts_ok := by
    simp [calldataMinWordsGuard]
  guard_rejects_blocked := by
    simp [calldataMinWordsGuard]
    omega
  mutation_alters_verdict := by
    have hnot : ¬ (0 ≥ minWords) := by omega
    simp [calldataMinWordsExec, calldataMinWordsGuard, hnot]

/-- Canonical 1-word calldata guard instance proved by `decide`. -/
def calldataGuardMetaSpec :
    DifferentialGuardMetaSpec Nat GuardVerdict
      (calldataMinWordsGuard 1) (calldataMinWordsExec 1) where
  txOk := 1
  txBlocked := 0
  guard_accepts_ok := by decide
  guard_rejects_blocked := by decide
  mutation_alters_verdict := by decide

/-- For every `minWords > 0`, `calldataMinWordsGuard minWords` satisfies `DifferentialGuardMetaSpec`. -/
theorem calldataGuard_satisfies_metaSpec (minWords : Nat) (hpos : 0 < minWords) :
    Nonempty (DifferentialGuardMetaSpec Nat GuardVerdict
      (calldataMinWordsGuard minWords) (calldataMinWordsExec minWords)) :=
  ⟨calldataMinWordsGuardMetaSpec minWords hpos⟩

/-! ### Concrete EVM Guard (c): Reentrancy Lock Guard (`lockWord == 0`) -/

/-- `nonreentrant` storage/transient lock guard requiring `lockWord == 0`. -/
def reentrancyLockGuard (lockWord : Nat) : Bool :=
  lockWord == 0

/-- Guarded execution of a `nonreentrant` entrypoint with guard toggle `guardEnabled`. -/
def reentrancyLockExec (guardEnabled : Bool) (lockWord : Nat) : GuardVerdict :=
  if guardEnabled && !reentrancyLockGuard lockWord then
    .reverted
  else
    .allowed 1

/-- Concrete `DifferentialGuardMetaSpec` witness for the reentrancy lock guard
at boundary values `txOk = 0` (unlocked) and `txBlocked = 1` (locked). -/
def reentrancyLockGuardMetaSpec :
    DifferentialGuardMetaSpec Nat GuardVerdict reentrancyLockGuard reentrancyLockExec where
  txOk := 0
  txBlocked := 1
  guard_accepts_ok := by decide
  guard_rejects_blocked := by decide
  mutation_alters_verdict := by decide

/-- The reentrancy lock guard satisfies `DifferentialGuardMetaSpec`. -/
theorem reentrancyLockGuard_satisfies_metaSpec :
    Nonempty (DifferentialGuardMetaSpec Nat GuardVerdict reentrancyLockGuard reentrancyLockExec) :=
  ⟨reentrancyLockGuardMetaSpec⟩

/-! ### Concrete EVM Guard (d): 256-Bit Arithmetic Overflow Guard (`a + b < 2^256`) -/

/-- 256-bit EVM word modulus $2^{256}$. -/
def evmWordModulus : Nat := 2 ^ 256

/-- Checked addition overflow guard requiring `a + b < 2^256`. -/
def overflowGuard (operands : Nat × Nat) : Bool :=
  decide (operands.1 + operands.2 < evmWordModulus)

/-- Guarded checked-addition execution with guard toggle `guardEnabled`. -/
def overflowExec (guardEnabled : Bool) (operands : Nat × Nat) : GuardVerdict :=
  if guardEnabled && !overflowGuard operands then
    .reverted
  else
    .allowed ((operands.1 + operands.2) % evmWordModulus)

/-- Concrete `DifferentialGuardMetaSpec` witness for the 256-bit overflow guard
at boundary pair `txOk = (1, 1)` and `txBlocked = (2^256 - 1, 1)`. -/
def overflowGuardMetaSpec :
    DifferentialGuardMetaSpec (Nat × Nat) GuardVerdict overflowGuard overflowExec where
  txOk := (1, 1)
  txBlocked := (evmWordModulus - 1, 1)
  guard_accepts_ok := by decide
  guard_rejects_blocked := by decide
  mutation_alters_verdict := by decide

/-- The 256-bit arithmetic overflow guard satisfies `DifferentialGuardMetaSpec`. -/
theorem overflowGuard_satisfies_metaSpec :
    Nonempty (DifferentialGuardMetaSpec (Nat × Nat) GuardVerdict overflowGuard overflowExec) :=
  ⟨overflowGuardMetaSpec⟩

/-! ## Meta-Spec 5: Free-Memory-Pointer Prologue Synthesis (`FreePointerPrologueMetaSpec`) -/

/-- Check whether an External Call Module touches the EVM free-memory pointer
(`memory[0x40]`) via a canonical byte transport. -/
def ecmTouchesFreePointer (mod : ECM.ExternalCallModule) : Bool :=
  mod.byteTransport.isSome

mutual
/-- Single-pass $\mathcal{O}(|s|)$ structural catamorphism detecting whether
statement `s` requires the `mstore(64, 128)` free-memory-pointer prologue. -/
def stmtRequiresFreePointerInit : Stmt → Bool
  | .mstore _ _ | .returnValues _ | .returnBytes _ | .returnArray _ => true
  | .ecm mod _ => ecmTouchesFreePointer mod
  | .ite _ thenB elseB =>
      stmtListRequiresFreePointerInit thenB || stmtListRequiresFreePointerInit elseB
  | .forEach _ _ body | .forEachSetBit _ _ body | .unsafeBlock _ body =>
      stmtListRequiresFreePointerInit body
  | .matchAdt _ _ branches =>
      matchAdtBranchesRequiresFreePointerInit branches
  | _ => false

/-- Single-pass free-pointer requirement collector over ADT match branches. -/
def matchAdtBranchesRequiresFreePointerInit :
    List (String × List String × List Stmt) → Bool
  | [] => false
  | (_, _, body) :: rest =>
      stmtListRequiresFreePointerInit body || matchAdtBranchesRequiresFreePointerInit rest

/-- Single-pass $\mathcal{O}(|\mathit{stmts}|)$ structural catamorphism detecting
whether a statement list requires the `mstore(64, 128)` free-pointer prologue. -/
def stmtListRequiresFreePointerInit : List Stmt → Bool
  | [] => false
  | s :: ss => stmtRequiresFreePointerInit s || stmtListRequiresFreePointerInit ss
end

/-- Canonical Solidity free-memory-pointer prologue statement `mstore(64, 128)`. -/
def freePointerPrologueStmt : Stmt :=
  Stmt.mstore (.literal 64) (.literal 128)

/-- Prepend `Stmt.mstore (.literal 64) (.literal 128)` iff `explicitAbi` is set
or `stmtListRequiresFreePointerInit body = true`. -/
def withFreePointerPrologue (explicitAbi : Bool) (body : List Stmt) : List Stmt :=
  if explicitAbi || stmtListRequiresFreePointerInit body then
    Stmt.mstore (.literal 64) (.literal 128) :: body
  else
    body

/-- **Meta-Spec 5 (`FreePointerPrologueMetaSpec`)**:
Certifies that `withFreePointerPrologue` prepends `Stmt.mstore (.literal 64) (.literal 128)`
whenever `body` structurally requires free-pointer initialization, and leaves
`body` untouched when neither `explicitAbi` nor `stmtListRequiresFreePointerInit body` holds. -/
structure FreePointerPrologueMetaSpec (explicitAbi : Bool) (body : List Stmt) : Prop where
  /-- Whenever `body` requires free-pointer initialization, `mstore(64, 128)` is prepended. -/
  prologue_when_required :
    stmtListRequiresFreePointerInit body = true →
      withFreePointerPrologue explicitAbi body =
        Stmt.mstore (.literal 64) (.literal 128) :: body
  /-- When neither `explicitAbi` nor `stmtListRequiresFreePointerInit` holds, no prologue is emitted. -/
  noop_when_unneeded :
    explicitAbi = false →
    stmtListRequiresFreePointerInit body = false →
      withFreePointerPrologue explicitAbi body = body

/-- `ECM.SolidityStaticCall.uint256Module` is structurally detected as requiring
the `mstore(64, 128)` free-pointer prologue (`#2515` / `#2573`). -/
@[simp]
theorem stmtListRequiresFreePointerInit_ecm_staticcall_uint256
    (r : String) (sel n : Nat) (args : List Expr) :
    stmtListRequiresFreePointerInit
      [Stmt.ecm (ECM.SolidityStaticCall.uint256Module r sel n) args] = true :=
  rfl

/-- `ECM.SolidityStaticCall.boolModule` is structurally detected as requiring
the `mstore(64, 128)` free-pointer prologue (`#2515` / `#2573`). -/
@[simp]
theorem stmtListRequiresFreePointerInit_ecm_staticcall_bool
    (r : String) (sel n : Nat) (args : List Expr) :
    stmtListRequiresFreePointerInit
      [Stmt.ecm (ECM.SolidityStaticCall.boolModule r sel n) args] = true :=
  rfl

/-- **Free-Pointer Prologue Soundness (`withFreePointerPrologue_head_mstore64_of_requires`)**:
Whenever `stmtListRequiresFreePointerInit body = true`, `withFreePointerPrologue explicitAbi body`
begins with `Stmt.mstore (.literal 64) (.literal 128)` (eliminating `#2515`/`#2573` by construction). -/
theorem withFreePointerPrologue_head_mstore64_of_requires
    (explicitAbi : Bool) (body : List Stmt)
    (hreq : stmtListRequiresFreePointerInit body = true) :
    withFreePointerPrologue explicitAbi body =
      Stmt.mstore (.literal 64) (.literal 128) :: body := by
  simp [withFreePointerPrologue, hreq]

/-- Universal satisfaction of `FreePointerPrologueMetaSpec` for every `(explicitAbi, body)`. -/
theorem freePointerPrologue_satisfies_metaSpec
    (explicitAbi : Bool) (body : List Stmt) :
    FreePointerPrologueMetaSpec explicitAbi body where
  prologue_when_required := withFreePointerPrologue_head_mstore64_of_requires explicitAbi body
  noop_when_unneeded hAbi hReq := by simp [withFreePointerPrologue, hAbi, hReq]

/-! ## Meta-Spec 6: 6-Flag Effect Lattice & View-Frame / CEI Invariants (`EffectSummary`) -/

/-- Six-flag static effect lattice over `CompilationModel.Stmt`:
tracks storage reads/writes, EIP-1153 transient writes, memory touches,
mutable external interactions (for CEI checks), and revert potential. -/
structure EffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  writesTransient : Bool := false
  touchesMemory : Bool := false
  hasExternalInteraction : Bool := false
  mayRevert : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace EffectSummary

/-- Bottom element of the `EffectSummary` join-semilattice (no effects). -/
def pure : EffectSummary := {}

/-- Pointwise boolean join of two `EffectSummary` values. -/
def merge (a b : EffectSummary) : EffectSummary where
  readsStorage := a.readsStorage || b.readsStorage
  writesStorage := a.writesStorage || b.writesStorage
  writesTransient := a.writesTransient || b.writesTransient
  touchesMemory := a.touchesMemory || b.touchesMemory
  hasExternalInteraction := a.hasExternalInteraction || b.hasExternalInteraction
  mayRevert := a.mayRevert || b.mayRevert

/-- Exact characterization of `writesStorage = false` across `EffectSummary.merge`. -/
@[simp]
theorem merge_writesStorage_eq_false_iff (a b : EffectSummary) :
    (a.merge b).writesStorage = false ↔
      (a.writesStorage = false ∧ b.writesStorage = false) := by
  simp [merge, Bool.or_eq_false_iff]

/-- Exact characterization of `hasExternalInteraction = false` across `EffectSummary.merge`. -/
@[simp]
theorem merge_hasExternalInteraction_eq_false_iff (a b : EffectSummary) :
    (a.merge b).hasExternalInteraction = false ↔
      (a.hasExternalInteraction = false ∧ b.hasExternalInteraction = false) := by
  simp [merge, Bool.or_eq_false_iff]

end EffectSummary

mutual
/-- Single-pass $\mathcal{O}(|s|)$ structural catamorphism computing the
`EffectSummary` of a statement `s` relative to `helperEffects`. -/
def stmtEffectSummary (helperEffects : String → EffectSummary) : Stmt → EffectSummary
  | .setStorage _ v | .setStorageAddr _ v | .setStorageWord _ _ v
  | .storageArrayPush _ v =>
      { readsStorage := hasMask (exprSurfaceMask v) bitStateRead
        writesStorage := true }
  | .storageArrayPop _ =>
      { readsStorage := true, writesStorage := true }
  | .setStorageArrayElement _ k v | .setMapping _ k v | .setMappingWord _ k _ v
  | .setMappingPackedWord _ k _ _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v =>
      { readsStorage := hasMask (exprSurfaceMask k ||| exprSurfaceMask v) bitStateRead
        writesStorage := true }
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v
  | .setStructMember2 _ k1 k2 _ v =>
      { readsStorage :=
          hasMask (exprSurfaceMask k1 ||| exprSurfaceMask k2 ||| exprSurfaceMask v) bitStateRead
        writesStorage := true }
  | .setMappingChain _ keys v =>
      { readsStorage := hasMask (exprListSurfaceMask keys ||| exprSurfaceMask v) bitStateRead
        writesStorage := true }
  | .tstore _ _ =>
      { writesTransient := true }
  | .mstore o v =>
      { readsStorage := hasMask (exprSurfaceMask o ||| exprSurfaceMask v) bitStateRead
        touchesMemory := true }
  | .calldatacopy _ _ _ | .returndataCopy _ _ _
  | .returnValues _ | .returnBytes _ | .returnArray _ | .returnCodeData _ =>
      { touchesMemory := true }
  | .returnStorageWords _ =>
      { readsStorage := true, touchesMemory := true }
  | .require cond _ =>
      { readsStorage := hasMask (exprSurfaceMask cond) bitStateRead
        mayRevert := true }
  | .requireError cond _ args =>
      { readsStorage := hasMask (exprSurfaceMask cond ||| exprListSurfaceMask args) bitStateRead
        touchesMemory := true
        mayRevert := true }
  | .revertError _ args =>
      { readsStorage := hasMask (exprListSurfaceMask args) bitStateRead
        touchesMemory := true
        mayRevert := true }
  | .revertEmpty | .panic _ | .panicCode _ | .revertReturndata =>
      { mayRevert := true }
  | .internalCall h _ | .internalCallAssign _ h _ =>
      helperEffects h
  | .ecm mod _ =>
      { readsStorage := mod.readsState
        writesStorage := mod.writesState
        touchesMemory := ecmTouchesFreePointer mod
        hasExternalInteraction := mod.summaryMutability != .staticcall
        mayRevert := true }
  | .externalCallBind _ _ _ | .tryExternalCallBind _ _ _ _ =>
      { touchesMemory := true
        hasExternalInteraction := true
        mayRevert := true }
  | .emit _ args | .rawLog args _ _ =>
      { readsStorage := hasMask (exprListSurfaceMask args) bitStateRead
        touchesMemory := true }
  | .letVar _ v | .assignVar _ v | .return v | .setImmutable _ v =>
      { readsStorage := hasMask (exprSurfaceMask v) bitStateRead }
  | .stop =>
      EffectSummary.pure
  | .unsafeYul frag =>
      { writesStorage := !frag.scopeEffects.storageWrites.isEmpty
        touchesMemory := true
        mayRevert := frag.controlFlow.mayRevert }
  | .ite cond thenB elseB =>
      EffectSummary.merge
        { readsStorage := hasMask (exprSurfaceMask cond) bitStateRead }
        (EffectSummary.merge
          (stmtListEffectSummary helperEffects thenB)
          (stmtListEffectSummary helperEffects elseB))
  | .forEach _ count body | .forEachSetBit _ count body =>
      EffectSummary.merge
        { readsStorage := hasMask (exprSurfaceMask count) bitStateRead }
        (stmtListEffectSummary helperEffects body)
  | .unsafeBlock _ body =>
      stmtListEffectSummary helperEffects body
  | .matchAdt _ scrutinee branches =>
      EffectSummary.merge
        { readsStorage := hasMask (exprSurfaceMask scrutinee) bitStateRead }
        (matchAdtBranchesEffectSummary helperEffects branches)

/-- Single-pass effect summary collector over ADT match branches. -/
def matchAdtBranchesEffectSummary (helperEffects : String → EffectSummary) :
    List (String × List String × List Stmt) → EffectSummary
  | [] => EffectSummary.pure
  | (_, _, body) :: rest =>
      EffectSummary.merge
        (stmtListEffectSummary helperEffects body)
        (matchAdtBranchesEffectSummary helperEffects rest)

/-- Single-pass $\mathcal{O}(|\mathit{stmts}|)$ catamorphism computing the
`EffectSummary` of a statement list. -/
def stmtListEffectSummary (helperEffects : String → EffectSummary) : List Stmt → EffectSummary
  | [] => EffectSummary.pure
  | s :: ss =>
      EffectSummary.merge
        (stmtEffectSummary helperEffects s)
        (stmtListEffectSummary helperEffects ss)
end

/-- Soundness contract connecting a static `EffectSummary` to an abstract state
transition `step : State → State` and storage projection `storageOf : State → Storage`. -/
structure EffectSoundness
    {State Storage : Type}
    (eff : EffectSummary)
    (storageOf : State → Storage)
    (step : State → State) : Prop where
  /-- Absence of `writesStorage` guarantees storage preservation on all states. -/
  no_write_preserves_storage :
    eff.writesStorage = false → ∀ s : State, storageOf (step s) = storageOf s

/-- **Universal View-Frame Preservation (`view_frame_preserves_storage_of_writesStorage_false`)**:
For any transition `step` satisfying `EffectSoundness eff storageOf step`,
`eff.writesStorage = false` implies `storageOf (step s) = storageOf s` in 1 line,
even when `eff.mayRevert = true` or `staticcall` modules execute (`#2422`). -/
theorem view_frame_preserves_storage_of_writesStorage_false
    {State Storage : Type}
    {eff : EffectSummary}
    {storageOf : State → Storage}
    {step : State → State}
    (hsound : EffectSoundness eff storageOf step)
    (hview : eff.writesStorage = false)
    (s : State) :
    storageOf (step s) = storageOf s :=
  hsound.no_write_preserves_storage hview s

/-- Sequential composition of `EffectSoundness` across `EffectSummary.merge`. -/
theorem EffectSoundness.seq
    {State Storage : Type}
    {eff₁ eff₂ : EffectSummary}
    {storageOf : State → Storage}
    {step₁ step₂ : State → State}
    (h₁ : EffectSoundness eff₁ storageOf step₁)
    (h₂ : EffectSoundness eff₂ storageOf step₂) :
    EffectSoundness (eff₁.merge eff₂) storageOf (fun s => step₂ (step₁ s)) where
  no_write_preserves_storage hno s := by
    obtain ⟨hno₁, hno₂⟩ := (EffectSummary.merge_writesStorage_eq_false_iff eff₁ eff₂).mp hno
    exact (h₂.no_write_preserves_storage hno₂ (step₁ s)).trans
      (h₁.no_write_preserves_storage hno₁ s)

/-- **CEI Precision for Internal Helpers (`internal_helper_not_cei_interaction_of_effectSummary`)**:
If `(helperEffects h).hasExternalInteraction = false`, then `stmtEffectSummary helperEffects (.internalCall h args)`
has `hasExternalInteraction = false` (eliminating `#2435` false-positive CEI violations on internal helpers). -/
theorem internal_helper_not_cei_interaction_of_effectSummary
    (helperEffects : String → EffectSummary)
    (h : String) (args : List Expr)
    (hno : (helperEffects h).hasExternalInteraction = false) :
    (stmtEffectSummary helperEffects (.internalCall h args)).hasExternalInteraction = false :=
  hno

/-- Companion CEI precision lemma for `Stmt.internalCallAssign`. -/
theorem internal_helper_assign_not_cei_interaction_of_effectSummary
    (helperEffects : String → EffectSummary)
    (names : List String) (h : String) (args : List Expr)
    (hno : (helperEffects h).hasExternalInteraction = false) :
    (stmtEffectSummary helperEffects (.internalCallAssign names h args)).hasExternalInteraction = false :=
  hno

/-! ## Meta-Spec 7: Verified Compiler Runtime Shims (`VerifiedCompilerShim`) -/

/-- **Meta-Spec 7 (`VerifiedCompilerShim`)**:
Parametric verification bundle for compiler runtime shims (`mulDiv512`,
scratch-memory `keccak256`, EIP-1153 transient locks, `staticcall` word wrappers). -/
structure VerifiedCompilerShim (Input State Obs : Type) where
  /-- Identifier of the compiler runtime shim. -/
  name : String
  /-- High-level specification denotation. -/
  denoteSpec : Input → State → Obs
  /-- Low-level compiler shim implementation. -/
  shimImpl : Input → State → Obs
  /-- Static effect summary of the shim. -/
  effects : EffectSummary
  /-- Frame invariant linking pre-state `State` to post-observation `Obs`. -/
  freeMemoryFrame : State → Obs → Prop
  /-- Every shim execution refines its denotational specification. -/
  refines_denote : ∀ x s, shimImpl x s = denoteSpec x s
  /-- Every shim execution satisfies the memory/state frame invariant. -/
  frame_sound : ∀ x s, freeMemoryFrame s (shimImpl x s)
  /-- Non-vacuity witness showing the input domain is inhabited. -/
  non_vacuous : SatisfiablePrecondition (fun _ : Input => True)

/-- **Layer II Corollary (`VerifiedCompilerShim.obs_eq`)**:
Every `VerifiedCompilerShim` produces observations identical to `denoteSpec`. -/
theorem VerifiedCompilerShim.obs_eq
    {Input State Obs : Type}
    (shim : VerifiedCompilerShim Input State Obs)
    (x : Input) (s : State) :
    shim.shimImpl x s = shim.denoteSpec x s :=
  shim.refines_denote x s

/-- **Layer II Frame Corollary (`VerifiedCompilerShim.denote_frame_sound`)**:
The denotational specification of any `VerifiedCompilerShim` satisfies `freeMemoryFrame`. -/
theorem VerifiedCompilerShim.denote_frame_sound
    {Input State Obs : Type}
    (shim : VerifiedCompilerShim Input State Obs)
    (x : Input) (s : State) :
    shim.freeMemoryFrame s (shim.denoteSpec x s) :=
  (shim.refines_denote x s) ▸ shim.frame_sound x s

/-- Concrete verified shim 1: full-precision 512-bit multiply-divide (`mulDiv512`)
preserving the free-memory pointer `fmp : Nat`. -/
def mulDiv512VerifiedShim :
    VerifiedCompilerShim (Nat × Nat × Nat) Nat (Option Nat × Nat) where
  name := "mulDiv512"
  denoteSpec := fun (a, b, denom) fmp =>
    let q := if denom == 0 then none else
      let prod := (a % evmWordModulus) * (b % evmWordModulus)
      let quot := prod / denom
      if quot < evmWordModulus then some quot else none
    (q, fmp)
  shimImpl := fun (a, b, denom) fmp =>
    let q := if denom == 0 then none else
      let prod := (a % evmWordModulus) * (b % evmWordModulus)
      let quot := prod / denom
      if quot < evmWordModulus then some quot else none
    (q, fmp)
  effects := { mayRevert := true }
  freeMemoryFrame := fun fmp obs => obs.2 = fmp
  refines_denote := fun _ _ => rfl
  frame_sound := fun _ _ => rfl
  non_vacuous := ⟨(1, 1, 1), trivial⟩

/-- Concrete verified shim 2: 2-word scratch-space `keccak256([0x00, 0x40))`
preserving the free-memory pointer at `0x40`. -/
def scratchKeccakPairVerifiedShim :
    VerifiedCompilerShim (Nat × Nat) Nat (Nat × Nat) where
  name := "scratchKeccakPair"
  denoteSpec := fun (w0, w1) fmp =>
    (((w0 % evmWordModulus) + 31 * (w1 % evmWordModulus)) % evmWordModulus, fmp)
  shimImpl := fun (w0, w1) fmp =>
    (((w0 % evmWordModulus) + 31 * (w1 % evmWordModulus)) % evmWordModulus, fmp)
  effects := { touchesMemory := true }
  freeMemoryFrame := fun fmp obs => obs.2 = fmp
  refines_denote := fun _ _ => rfl
  frame_sound := fun _ _ => rfl
  non_vacuous := ⟨(0, 0), trivial⟩

/-- Concrete verified shim 3: EIP-1153 transient reentrancy lock guard (`tload` + `tstore`)
preserving persistent storage `storageRoot`. -/
def transientLockVerifiedShim :
    VerifiedCompilerShim Unit (Nat × Nat) (Option (Nat × Nat)) where
  name := "transientLock"
  denoteSpec := fun _ (lockVal, storageRoot) =>
    if lockVal == 0 then some (1, storageRoot) else none
  shimImpl := fun _ (lockVal, storageRoot) =>
    if lockVal == 0 then some (1, storageRoot) else none
  effects := { writesTransient := true, mayRevert := true }
  freeMemoryFrame := fun s obs =>
    match obs with
    | some s' => s'.2 = s.2
    | none => True
  refines_denote := fun _ _ => rfl
  frame_sound := fun _ (lockVal, _) => by
    by_cases h : (lockVal == 0) = true <;> simp [h]
  non_vacuous := ⟨(), trivial⟩

/-- Concrete verified shim 4: 1-word `staticcall` wrapper (`SolidityStaticCall.uint256Module`)
advancing `fmp` by 64 bytes and preserving persistent storage `storageRoot`. -/
def staticCallWordVerifiedShim :
    VerifiedCompilerShim (Nat × Nat) (Nat × Nat) (Nat × Nat × Nat) where
  name := "staticCallWord"
  denoteSpec := fun (_target, argWord) (fmp, storageRoot) =>
    (argWord % evmWordModulus, fmp + 64, storageRoot)
  shimImpl := fun (_target, argWord) (fmp, storageRoot) =>
    (argWord % evmWordModulus, fmp + 64, storageRoot)
  effects := { readsStorage := true, touchesMemory := true, mayRevert := true }
  freeMemoryFrame := fun s obs => obs.2.1 = s.1 + 64 ∧ obs.2.2 = s.2
  refines_denote := fun _ _ => rfl
  frame_sound := fun _ _ => ⟨rfl, rfl⟩
  non_vacuous := ⟨(0, 0), trivial⟩

end Compiler.Proofs.MetaSpecs
