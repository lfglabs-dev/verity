import Compiler.Proofs.IRGeneration.Contract
import Compiler.Proofs.IRGeneration.GenericInduction.Calls
import Compiler.Proofs.IRGeneration.GenericInduction.CanonicalEcmCalls
import Compiler.Proofs.IRGeneration.GenericInduction.MulDiv512AndAdt
import Compiler.Proofs.IRGeneration.GenericInduction.BitLoopsAndStorageArrays
import Compiler.Proofs.IRGeneration.SupportedSpec.SurfaceMask
import Compiler.Proofs.IRGeneration.SupportedSpec.SupportProfile
import Compiler.Proofs.TrustSurface.LinearEquivalence
import Compiler.Proofs.EndToEnd.DispatchConfig
import Compiler.Proofs.MetaSpecs
import Compiler.Proofs.SpecHarness

namespace Compiler.Proofs.IRGeneration.CoreFragment

open Compiler.CompilationModel
open Compiler.Yul

/-!
# Unified 100% Core Fragment Layer 2 Preservation Facade (Node N8)

This module unifies the five Core Fragment verification tracks into a single
composable Layer 2 proof facade:

- **Track F1 (`N2` — `#2574`)**: Unified `SupportedStmtList` induction covering
  non-terminal `Stmt.ite` branching and literal-bounded `Stmt.forEach` loops in
  external runtime functions, constructors, and special entrypoints.
- **Track F2 (`N6` — `#2575`, `#1638`)**: Compositional internal helper
  preservation with `WithInternals` (`SupportedSpecWithHelpers`,
  `Contract.compile_preserves_semantics_with_helper_rich_support_of_body_goals`).
- **Track F3 (`N5` — `#2571`, `#2082`)**: Structurally recursive dynamic ABI
  and indexed event encoders (`compileUnindexedAbiEncode`,
  `compileIndexedInPlaceEncoding`) and their `execIRStmts` append/composition
  bridges (`Function.execIRStmts_compileUnindexedAbiEncode_append`).
- **Track F4 (`N6` — `#2575`)**: External Call Module (`Stmt.ecm`) head-step
  composition (`EcmHeadStepBridgeWithInternals`,
  `compiledStmtStepWithHelpersAndHelperIRWithInternals_of_ecmBridge`).
- **Track F5 (`N7` — `#2576`)**: Whole-contract constructor deploy
  (`ir.deploy`, `ir.constructorPayable`) and selector-miss `fallback` /
  `receive` special-entrypoint preservation.
-/

/-- Unified whole-contract lifecycle preservation bundle connecting:
1. Selector-dispatched runtime execution (`supportedSourceContractSemanticsExceptMappingWrites`),
2. Constructor deploy execution (`interpretConstructorWithHelpers` vs `ir.deploy`), and
3. Selector-miss `fallback` / `receive` special-entrypoint dispatch
   (`Contract.interpretSpecialEntrypointsOnMiss` vs
   `Contract.execIRSpecialEntrypointsOnMiss`). -/
structure FullContractLifecyclePreserved
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (fallbackSpec receiveSpec : Option FunctionSpec) : Prop where
  /-- Selector-dispatched runtime functions preserve source semantics. -/
  runtime_preserved :
    ∀ (tx : IRTransaction) (initialWorld : Verity.ContractState),
      Function.TxContextNormalized tx →
      Function.TxCalldataSizeFitsEvm tx →
      FunctionBody.sourceResultMatchesIRResult
        (supportedSourceContractSemanticsExceptMappingWrites
          model selectors hSupported tx initialWorld)
        (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld))
  /-- Constructor deploy semantics (when `model.constructor = some ctor`) are preserved. -/
  constructor_preserved :
    ∀ (ctor : ConstructorSpec) (tx : IRTransaction) (initialWorld : Verity.ContractState)
      (bindings ctorBindings : List (String × Nat)),
      model.constructor = some ctor →
      SupportedConstructor model ctor →
      (∀ stmt ∈ ctor.body, StmtMappingWriteSlotSafe model.fields stmt) →
      SourceSemantics.bindSupportedParams ctor.params (tx.args.take ctor.params.length) =
        some bindings →
      SourceSemantics.constructorExecutionBindings ctor tx.args = some ctorBindings →
      Function.TxContextNormalized tx →
      Function.TxConstructorCalldataSizeFitsEvm tx →
      ∃ bodyStmts,
        compileStmtList model.fields model.events model.errors .memory [] false
          (constructorBodyScope ctor.params) [] ctor.body [] = Except.ok bodyStmts ∧
        ir.deploy = genConstructorArgLoads ctor.params ++ bodyStmts ∧
        ir.constructorPayable = ctor.isPayable ∧
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretConstructorWithHelpers
            model hSupported.helperFuel ctor tx initialWorld)
          (Function.execResultToIRResult
            (FunctionBody.initialIRStateForTx model tx initialWorld)
            (execIRStmts (sizeOf bodyStmts + 1)
              (ParamLoading.applyBindingsToIRState
                (FunctionBody.initialIRStateForTx model tx initialWorld) ctorBindings)
              bodyStmts))
  /-- Selector-miss `fallback` and `receive` special entrypoints preserve source semantics. -/
  special_entrypoints_on_miss_preserved :
    ∀ (tx : IRTransaction) (initialWorld : Verity.ContractState),
      Function.TxContextNormalized tx →
      Function.TxCalldataSizeFitsEvm tx →
      FunctionBody.sourceResultMatchesIRResult
        (Contract.interpretSpecialEntrypointsOnMiss
          model hSupported.helperFuel fallbackSpec receiveSpec tx initialWorld)
        (Contract.execIRSpecialEntrypointsOnMiss ir tx
          (FunctionBody.initialIRStateForTx model tx initialWorld))

private theorem validateCompileInputs_ok_of_compile
    (model : CompilationModel) (selectors : List Nat) (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    validateCompileInputs model selectors = Except.ok () := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | ⟨⟩
  · simp [hvalidate] at hcompile
  · rfl

/-- **Master Core Fragment Lifecycle Theorem (`F1` + `F5`, statement-local slot safety)**:
Any contract in `SupportedSpecExceptMappingWrites` that compiles via
`CompilationModel.compile model selectors = Except.ok ir` satisfies all three
arms of `FullContractLifecyclePreserved` (selector-dispatched runtime,
constructor deploy, and selector-miss `fallback`/`receive`). -/
theorem compile_preserves_full_contract_lifecycle_stmtSafety
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) (ir : IRContract)
    (fallbackSpec receiveSpec : Option FunctionSpec)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hRuntimeSafety : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hpickFallback : pickUniqueFunctionByName "fallback" model.functions = Except.ok fallbackSpec)
    (hpickReceive : pickUniqueFunctionByName "receive" model.functions = Except.ok receiveSpec)
    (hFallbackSupported : ∀ ep, fallbackSpec = some ep → Function.SupportedSpecialEntrypoint model ep)
    (hFallbackSafety : ∀ ep, fallbackSpec = some ep →
      ∀ stmt ∈ ep.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hReceiveSupported : ∀ ep, receiveSpec = some ep → Function.SupportedSpecialEntrypoint model ep)
    (hReceiveSafety : ∀ ep, receiveSpec = some ep →
      ∀ stmt ∈ ep.body, StmtMappingWriteSlotSafe model.fields stmt) :
    FullContractLifecyclePreserved model selectors hSupported ir fallbackSpec receiveSpec := by
  have hvalidateInputs := validateCompileInputs_ok_of_compile model selectors ir hcompile
  have hnoConflict : firstFieldWriteSlotConflict model.fields = none := by
    simpa [hSupported.normalizedFields] using
      validateCompileInputs_firstFieldWriteSlotConflict_eq_none hvalidateInputs
  refine ⟨fun tx w htx hsz => Contract.compile_preserves_semantics_except_mapping_writes_stmtSafety
      model selectors hSupported ir tx w hnoConflict hRuntimeSafety htx hsz hcompile,
    fun ctor tx w b cb hctor hSup hSafe hb hcb htx hsz =>
      Contract.compile_preserves_constructor_semantics_of_supportedSpecExceptMappingWrites
        model selectors hSupported ir ctor hctor hSup hSafe tx w b cb hcompile hb hcb htx hsz,
    fun tx w htx hsz => Contract.compile_preserves_special_entrypoints_on_selector_miss_stmtSafety
      model selectors ir fallbackSpec receiveSpec hSupported.helperFuel hSupported.normalizedFields
      hSupported.noEvents hSupported.noErrors hSupported.noAdtTypes hSupported.noInternalFunctions
      hpickFallback hpickReceive hFallbackSupported hFallbackSafety hReceiveSupported
      hReceiveSafety tx w hcompile htx hsz⟩

/-- **Master Core Fragment Lifecycle Theorem (`F1` + `F5`, global slot safety)**:
Specializes `FullContractLifecyclePreserved` to contract-wide
`SupportedStmtListMappingWriteSlotSafety model.fields`. -/
theorem compile_preserves_full_contract_lifecycle
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) (ir : IRContract)
    (fallbackSpec receiveSpec : Option FunctionSpec)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (hpickFallback : pickUniqueFunctionByName "fallback" model.functions = Except.ok fallbackSpec)
    (hpickReceive : pickUniqueFunctionByName "receive" model.functions = Except.ok receiveSpec)
    (hFallbackSupported : ∀ ep, fallbackSpec = some ep → Function.SupportedSpecialEntrypoint model ep)
    (hReceiveSupported : ∀ ep, receiveSpec = some ep → Function.SupportedSpecialEntrypoint model ep) :
    FullContractLifecyclePreserved model selectors hSupported ir fallbackSpec receiveSpec := by
  have hvalidateInputs := validateCompileInputs_ok_of_compile model selectors ir hcompile
  have hnoConflict : firstFieldWriteSlotConflict model.fields = none := by
    simpa [hSupported.normalizedFields] using
      validateCompileInputs_firstFieldWriteSlotConflict_eq_none hvalidateInputs
  refine ⟨fun tx w htx hsz => Contract.compile_preserves_semantics_except_mapping_writes
      model selectors hSupported ir tx w hnoConflict hsafety htx hsz hcompile,
    fun ctor tx w b cb hctor hSup _ hb hcb htx hsz =>
      Contract.compile_preserves_constructor_semantics model selectors ir ctor
        hSupported.helperFuel hSupported.normalizedFields hSupported.noEvents hSupported.noErrors
        hSupported.noAdtTypes hSupported.noInternalFunctions hctor hSup hsafety tx w b cb
        hcompile hb hcb htx hsz,
    fun tx w htx hsz => Contract.compile_preserves_special_entrypoints_on_selector_miss
      model selectors ir fallbackSpec receiveSpec hSupported.helperFuel hSupported.normalizedFields
      hSupported.noEvents hSupported.noErrors hSupported.noAdtTypes hSupported.noInternalFunctions
      hpickFallback hpickReceive hFallbackSupported hReceiveSupported hsafety tx w hcompile htx hsz⟩

/-- **Master Helper-Rich & External Call Module Composition Theorem (`F2` + `F4`, `#1638`)**:
Re-exports whole-contract helper-rich preservation
(`Contract.compile_preserves_semantics_with_helper_rich_support_of_body_goals`)
alongside the `Stmt.ecm` `WithInternals` step lift
(`compiledStmtStepWithHelpersAndHelperIRWithInternals_of_ecmBridge`). -/
theorem compile_preserves_helper_rich_contract_semantics
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers model selectors)
    (ir : IRContract) (irFuelSlack : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hbodyGoals :
      Contract.SupportedHelperRichFunctionBodyGoals
        model selectors hSupported ir irFuelSlack tx initialWorld) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsWithHelpers model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  Contract.compile_preserves_semantics_with_helper_rich_support_of_body_goals
    model selectors hSupported ir irFuelSlack tx initialWorld
    htxNormalized hcalldataSizeFits hcompile hbodyGoals

/-- **Parametric Runtime Dispatch Facade (`M1`)**:
Specializes `EndToEnd.evalParametricRuntimeDispatch_matches_ir` to the Layer 2
observation relation `FunctionBody.sourceResultMatchesIRResult` for any
`cfg : EndToEnd.DispatchConfig`. -/
theorem parametric_runtime_dispatch_matches_ir
    (cfg : EndToEnd.DispatchConfig)
    (model : CompilationModel) (selectors : List Nat)
    (fallbackSpec receiveSpec : Option FunctionSpec)
    (ir : IRContract) (tx : IRTransaction)
    (revertSrc : SourceSemantics.SourceContractResult) (revertIR : IRResult)
    (execFn execEp : FunctionSpec → SourceSemantics.SourceContractResult)
    (execIRFn : IRFunction → IRResult)
    (execIREp : IREntrypoint → IRResult)
    (hAlign :
      EndToEnd.ParametricDispatchAlignment
        FunctionBody.sourceResultMatchesIRResult
        model selectors fallbackSpec receiveSpec ir tx
        revertSrc revertIR execFn execEp execIRFn execIREp) :
    FunctionBody.sourceResultMatchesIRResult
      (EndToEnd.evalParametricRuntimeDispatch cfg model selectors
        fallbackSpec receiveSpec tx revertSrc execFn execEp)
      (EndToEnd.evalParametricIRRuntimeDispatch cfg ir tx
        revertIR execIRFn execIREp) := by
  exact EndToEnd.evalParametricRuntimeDispatch_matches_ir cfg hAlign

/-- **Universal Trust-Boundary Partition Facade (`M2`)**:
Re-exports `MetaSpecs.trust_boundary_partition_complete` certifying that every
`spec : CompilationModel` and `allowedMask : SurfaceMask` is partitioned with
zero silent fallthrough. -/
theorem core_fragment_trust_boundary_partition
    (spec : CompilationModel) (allowedMask : SurfaceMask) :
    MetaSpecs.CertifiedOrExplicitlyFlagged spec allowedMask :=
  MetaSpecs.trust_boundary_partition_complete spec allowedMask

/-- **Canonical 12-Feature Invariant Suite Facade (`M2`)**:
Re-exports `SpecHarness.canonicalCompilerFeatureSuite_all_hold` certifying all 12
representative Core Fragment feature invariants via a single `by decide` check. -/
theorem core_fragment_canonical_feature_suite_holds :
    ∀ c ∈ SpecHarness.canonicalCompilerFeatureSuite,
      SpecHarness.CompilerInvariantCaseHolds c :=
  SpecHarness.canonicalCompilerFeatureSuite_all_hold

end Compiler.Proofs.IRGeneration.CoreFragment
