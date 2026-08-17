import Compiler.Proofs.IRGeneration.GuardedDispatch
import Compiler.Proofs.IRGeneration.Contract

/-!
# `SupportedSpecGuarded` and the erasure-free compile decomposition

The guarded counterpart of `SupportedSpec`: identical global invariants,
surface gates, and constructor support, but per-function support drops the
`noNonReentrant` boundary in favor of lock resolvability (vacuous for
unannotated functions, so every `SupportedSpec` embeds).  The compile
decomposition then characterizes `ir.functions` by the *guarded* pipeline —
no lock-free rewrite — feeding the generic dispatcher instance (#2314).
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.Contract

/-- Per-function support for the guarded family: `SupportedFunction` minus
the `noNonReentrant` boundary, plus lock resolvability (vacuously true for
unannotated functions). -/
structure SupportedFunctionGuarded (spec : CompilationModel)
    (fn : FunctionSpec) where
  nonInternal : fn.isInternal = false
  nonSpecialEntrypoint : isInteropEntrypointName fn.name = false
  lockResolved : ∀ lockField, fn.nonReentrantLock = some lockField →
    ∃ field slot,
      findFieldWithResolvedSlot spec.fields lockField = some (field, slot) ∧
        slot < Compiler.Constants.evmModulus
  params : SupportedParamProfile fn.params
  returns : SupportedReturnProfile fn
  body : SupportedBodyInterface spec fn

/-- Whole-contract guarded support inventory. -/
structure SupportedSpecGuarded (spec : CompilationModel)
    (selectors : List Nat) where
  invariants : SupportedSpecInvariants spec selectors
  surface : SupportedSpecSurface spec
  constructor :
    ∀ ctor, spec.constructor = some ctor → SupportedConstructor spec ctor
  functions :
    ∀ fn, fn ∈ spec.functions → SupportedFunctionGuarded spec fn

/-- Every lock-free supported function is guarded-supported. -/
def SupportedFunction.toGuarded {spec : CompilationModel} {fn : FunctionSpec}
    (h : SupportedFunction spec fn) : SupportedFunctionGuarded spec fn where
  nonInternal := h.nonInternal
  nonSpecialEntrypoint := h.nonSpecialEntrypoint
  lockResolved := fun lockField hlock => by
    rw [h.noNonReentrant] at hlock
    cases hlock
  params := h.params
  returns := h.returns
  body := h.body

/-- Every supported spec is guarded-supported. -/
def SupportedSpec.toGuarded {spec : CompilationModel} {selectors : List Nat}
    (h : SupportedSpec spec selectors) : SupportedSpecGuarded spec selectors where
  invariants := h.invariants
  surface := h.surface
  constructor := h.constructor
  functions := fun fn hmem => (h.functions fn hmem).toGuarded

theorem SupportedSpecGuarded.noInternalFunctions
    {spec : CompilationModel} {selectors : List Nat}
    (h : SupportedSpecGuarded spec selectors) :
    ∀ fn ∈ spec.functions, fn.isInternal = false :=
  fun fn hmem => (h.functions fn hmem).nonInternal

/-- Erasure-free compile decomposition: `ir.functions` characterized by the
guarded pipeline. -/
theorem compileValidatedCore_ok_yields_guarded_functions
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecGuarded model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun (entry : FunctionSpec × Nat) irFn =>
        compileGuardedFunctionSpec model.fields model.events model.errors []
          [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.surface.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.surface.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_all_nonInternal model.functions
      hSupported.noInternalFunctions
  unfold compileValidatedCore at hcore
  rw [hSupported.invariants.normalizedFields,
    hSupported.surface.noAdtTypes, hSupported.surface.noEvents,
    hSupported.surface.noErrors,
    hnoInternalFns, hfallback, hreceive,
    hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileGuardedFunctionSpec model.fields [] [] [] [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    rcases hctor :
        compileConstructor model.fields [] [] [] model.constructor with _ | deployStmts
    · simp [hctor] at hcore
      cases hcore
    · simp [hctor] at hcore
      have hfunctions : ir.functions = irFns := by
        injection hcore with hir
        cases hir
        rfl
      have hcompiled :
          List.Forall₂
            (fun (entry : FunctionSpec × Nat) irFn =>
              compileGuardedFunctionSpec model.fields model.events model.errors []
                [] entry.2 entry.1 = Except.ok irFn)
            ((model.functions.filter
                (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors)
            irFns := by
        simpa [hSupported.surface.noEvents, hSupported.surface.noErrors] using
          (guarded_functions_forall₂_of_mapM_ok model.fields [] [] [] _ _ hmap)
      simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
        hfunctions] using hcompiled

/-- Compile-level wrapper. -/
theorem compile_ok_yields_guarded_functions
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecGuarded model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun (entry : FunctionSpec × Nat) irFn =>
        compileGuardedFunctionSpec model.fields model.events model.errors []
          [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_guarded_functions
      model selectors hSupported ir hcompile

end Compiler.Proofs.IRGeneration
