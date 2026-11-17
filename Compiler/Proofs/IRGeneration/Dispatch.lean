import Compiler.Proofs.IRGeneration.DispatchGeneric

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace Dispatch

theorem runtimeContractOfFunctions_legacyCompatible
    (name : String) (functions : List IRFunction)
    (hlegacyBodies : ∀ fn ∈ functions, LegacyCompatibleExternalStmtList fn.body) :
    LegacyCompatibleRuntimeContract (runtimeContractOfFunctions name functions) := by
  refine ⟨runtimeContractOfFunctions_internalFunctions name functions, ?_⟩
  intro fn hmem
  exact hlegacyBodies fn hmem

theorem runtimeContractOfFunctions_disjoint
    (name : String) (functions : List IRFunction)
    (hdisjointBodies :
      ∀ fn ∈ functions,
        YulStmtListCallsDisjointFromInternalTable
          (runtimeContractOfFunctions name functions)
          fn.body) :
    DisjointRuntimeContract (runtimeContractOfFunctions name functions) := by
  intro fn hmem
  exact hdisjointBodies fn hmem

/-- A function compiled by `compileFunctionSpec` (standard ABI decoding) has the
declared parameters and a body that starts with the generated parameter
loads. -/
theorem compileFunctionSpec_ok_loads_prefix
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (internalFunctions : List FunctionSpec) (sel : Nat) (fn : FunctionSpec) (irFn : IRFunction)
    (habi : fn.abiDecoding = .standard)
    (hcompile : compileFunctionSpec fields events errors [] sel fn
      (internalFunctions := internalFunctions) = Except.ok irFn) :
    irFn.params = fn.params.map Param.toIRParam ∧
      ∃ rest, irFn.body = genParamLoads fn.params ++ rest := by
  obtain ⟨returns, bodyStmts, -, -, -, rfl⟩ :=
    FunctionShape.compileFunctionSpec_ok_components_with_internals fields events errors []
      internalFunctions sel fn irFn hcompile
  exact ⟨rfl, bodyStmts, by
    simp [FunctionShape.compiledFunctionIR, FunctionSpec.bindingParams, habi]⟩

/-- The IR rollback record for a transaction matches the reverted source
result. -/
theorem reverted_matches_initial_rollback
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
      { success := false, returnValue := none
        finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
        finalMappings := Compiler.Proofs.storageAsMappings
          (FunctionBody.initialIRStateForTx model tx initialWorld).storage
        events := (FunctionBody.initialIRStateForTx model tx initialWorld).events } := by
  simp [FunctionBody.sourceResultMatchesIRResult,
    SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
    FunctionBody.encodeStorage_withTransactionContext,
    FunctionBody.encodeEvents_withTransactionContext]

/-- A function whose body starts with the generated loads reverts like the
source when binding rejects arguments covering every parameter (a dirty scalar
word). -/
theorem execIRFunction_bindFail_matches
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (fn : FunctionSpec) (irFn : IRFunction)
    (hshape : irFn.params = fn.params.map Param.toIRParam ∧
      ∃ rest, irFn.body = genParamLoads fn.params ++ rest)
    (hsupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hlen : fn.params.length ≤ tx.args.length)
    (hnone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  obtain ⟨hparams, rest, hbody⟩ := hshape
  have h := Function.execIRFunction_revert_of_bind_none
    (FunctionBody.initialIRStateForTx model tx initialWorld) irFn fn.params rest hparams hbody
    hsupported hlen hnone
  rw [show tx.args = (FunctionBody.initialIRStateForTx model tx initialWorld).calldata from rfl, h]
  exact reverted_matches_initial_rollback model tx initialWorld

/-- Helper-aware analogue of `execIRFunction_bindFail_matches`, for a runtime
contract whose helper names are reserved (so the loads call no helper). -/
theorem execIRFunctionWithInternals_bindFail_matches
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (runtimeContract : IRContract) (helperFuel : Nat)
    (hreserved : InternalTableNamesReserved runtimeContract)
    (fn : FunctionSpec) (irFn : IRFunction)
    (hshape : irFn.params = fn.params.map Param.toIRParam ∧
      ∃ rest, irFn.body = genParamLoads fn.params ++ rest)
    (hsupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hlen : fn.params.length ≤ tx.args.length)
    (hnone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
      (execIRFunctionWithInternals runtimeContract helperFuel irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  obtain ⟨hparams, rest, hbody⟩ := hshape
  have h := Function.execIRFunctionWithInternals_revert_of_bind_none runtimeContract helperFuel
    (FunctionBody.initialIRStateForTx model tx initialWorld) irFn fn.params rest hparams hbody
    hsupported hlen hnone
    (Function.genParamLoads_callsDisjoint_of_reserved runtimeContract fn.params hsupported hreserved)
  rw [show tx.args = (FunctionBody.initialIRStateForTx model tx initialWorld).calldata from rfl, h]
  exact reverted_matches_initial_rollback model tx initialWorld

theorem interpretContract_correct_of_compiled_functions
    (model : CompilationModel)
    {habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard}
    (selectors : List Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn => compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  interpretContract_correct_of_functions_generic (habi := habi)
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    model selectors irFns tx initialWorld
    (fun fn sel irFn hP => by
      obtain ⟨hp, hs, hpay⟩ := Function.compileFunctionSpec_ok_metadata_with_internals
        model.fields model.events model.errors sel fn irFn [] hP
      exact ⟨hp, hs, hpay⟩)
    hcompiled hparamsSupported
    (fun fn sel irFn hfn hP hlen hnone => execIRFunction_bindFail_matches model tx initialWorld
      fn irFn (compileFunctionSpec_ok_loads_prefix _ _ _ [] sel fn irFn (habi fn hfn) hP)
      (hparamsSupported fn hfn) hlen hnone)
    hfunction

/-- Under standard ABI decoding of supported scalar params, `interpretFunction`
reverts whenever scalar binding fails. -/
private theorem interpretFunction_reverted_of_standard_bind_none
    {model : CompilationModel} (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (fn : FunctionSpec) (hmem : fn ∈ selectorDispatchedFunctions model)
    (hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    SourceSemantics.interpretFunction model fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) :=
  interpretFunction_eq_reverted_of_bind_none model fn tx initialWorld
    (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hparamsSupported fn hmem)
    (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hbindNone)

theorem interpretContractWithInternals_correct_of_compiled_functions
    (model : CompilationModel)
    {habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard}
    (selectors : List Nat) (runtimeContract : IRContract) (irFuelSlack : Nat)
    (irFns : List IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hfunctions : runtimeContract.functions = irFns)
    (hreserved : InternalTableNamesReserved runtimeContract)
    (hcompiled : List.Forall₂ (fun entry irFn => compileFunctionSpec model.fields model.events
        model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretContract_eq_interpretContractWith]
  refine interpretContractWith_correct_generic
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (fun fn => SourceSemantics.interpretFunction model fn tx initialWorld) _
    model selectors irFns tx initialWorld _
    (fun _ _ _ hP => Function.compileFunctionSpec_ok_metadata_with_internals _ _ _ _ _ _ _ hP)
    (interpretFunction_reverted_of_standard_bind_none tx initialWorld habi hparamsSupported)
    hcompiled hparamsSupported
    (fun fn sel irFn hfn hP hlen hnone => execIRFunctionWithInternals_bindFail_matches model tx
      initialWorld runtimeContract irFuelSlack hreserved fn irFn
      (compileFunctionSpec_ok_loads_prefix _ _ _ [] sel fn irFn (habi fn hfn) hP)
      (hparamsSupported fn hfn) hlen hnone) ?_ hfunction
  simp [interpretIRWithInternals, hfunctions, FunctionBody.initialIRStateForTx]
  congr

/-- Under standard ABI decoding of supported scalar params,
`interpretFunctionWithHelpers` reverts whenever scalar binding fails. -/
private theorem interpretFunctionWithHelpers_reverted_of_standard_bind_none
    {model : CompilationModel} (helperFuel : Nat) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (fn : FunctionSpec) (hmem : fn ∈ selectorDispatchedFunctions model)
    (hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) :=
  interpretFunctionWithHelpers_eq_reverted_of_bind_none model helperFuel fn tx initialWorld
    (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hparamsSupported fn hmem)
    (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hbindNone)

/-- Helper-aware dispatch skeleton.  This is the populated-runtime analogue of
`interpretContractWithInternals_correct_of_compiled_functions`, but it keeps
`interpretContractWithHelpers`/`interpretFunctionWithHelpers` all the way
through and therefore does not reduce helper callers to legacy semantics. -/
theorem interpretContractWithHelpersWithInternals_correct_of_compiled_functions
    (model : CompilationModel)
    {habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard}
    (selectors : List Nat) (helperFuel : Nat) (runtimeContract : IRContract)
    (irFuelSlack : Nat) (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (hfunctions : runtimeContract.functions = irFns)
    (hreserved : InternalTableNamesReserved runtimeContract)
    (hcompiled : List.Forall₂ (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1
          (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn
          (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
          (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContractWithHelpers
        model selectors helperFuel tx initialWorld)
      (interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretContractWithHelpers_eq_interpretContractWith]
  refine interpretContractWith_correct_generic
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn
        (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn)
    (fun fn => SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
    _ model selectors irFns tx initialWorld _
    (fun _ _ _ hP => Function.compileFunctionSpec_ok_metadata_with_internals _ _ _ _ _ _ _ hP)
    (interpretFunctionWithHelpers_reverted_of_standard_bind_none helperFuel tx initialWorld
      habi hparamsSupported)
    hcompiled hparamsSupported
    (fun fn sel irFn hfn hP hlen hnone => execIRFunctionWithInternals_bindFail_matches model tx
      initialWorld runtimeContract irFuelSlack hreserved fn irFn
      (compileFunctionSpec_ok_loads_prefix _ _ _ _ sel fn irFn (habi fn hfn) hP)
      (hparamsSupported fn hfn) hlen hnone) ?_ hfunction
  simp [interpretIRWithInternals, hfunctions, FunctionBody.initialIRStateForTx]
  congr

/-- Dispatch consumer specialized to the new helper-rich support inventory. -/
theorem interpretContractWithInternals_correct_of_compiled_functions_with_helper_rich_support
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers model selectors)
    (runtimeContract : IRContract)
    (irFuelSlack : Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : runtimeContract.functions = irFns)
    (hreserved : InternalTableNamesReserved runtimeContract)
    (hcompiled :
      List.Forall₂
        (fun entry irFn => compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1
          (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn
          (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsWithHelpers
            model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsWithHelpers
        model selectors hSupported tx initialWorld)
      (interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContractWithHelpersWithInternals_correct_of_compiled_functions
    (habi := fun _ hfn => (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
    model selectors hSupported.helperFuel runtimeContract irFuelSlack irFns tx initialWorld
    hfunctions hreserved hcompiled (fun fn hfn => hSupported.selectorFunctionParamsSupported hfn)
    (by
      intro fn sel irFn bindings hfn hcompile hbind
      simpa [supportedSourceFunctionSemanticsWithHelpers] using
        hfunction fn sel irFn bindings hfn hcompile hbind)

private theorem legacy_function_correct_of_supportedSourceFunctionSemantics
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args
          (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  intro fn sel irFn bindings hfn hcompileFn hbind
  simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using
    hfunction fn sel irFn bindings hfn hcompileFn hbind

/-- Helper-proof-carrying wrapper for the dispatch theorem.
The current proof still reduces helper-aware source semantics to the legacy
helper-free semantics via the helper-excluding `SupportedStmtList` body
fragment, so the additional helper proof slot is present to stabilize the
theorem boundary rather than to widen the proved fragment today. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompiled : List.Forall₂ (fun entry irFn => compileFunctionSpec model.fields model.events
        model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy := interpretContract_correct_of_compiled_functions
    (habi := fun _ hfn => (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
    model selectors irFns tx initialWorld hcompiled hparamsSupported
    (legacy_function_correct_of_supportedSourceFunctionSemantics
      model selectors hSupported tx initialWorld hfunction)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld, sourceContractSemantics] using hlegacy

/-- Populated-runtime, slack-indexed dispatch consumer for helper-aware
per-function correctness results. -/
theorem interpretContractWithInternals_correct_of_compiled_functions_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (runtimeContract : IRContract)
    (irFuelSlack : Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : runtimeContract.functions = irFns)
    (hreserved : InternalTableNamesReserved runtimeContract)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy := interpretContractWithInternals_correct_of_compiled_functions
    (habi := fun _ hfn => (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
    model selectors runtimeContract irFuelSlack irFns tx initialWorld hfunctions hreserved
    hcompiled hparamsSupported (by
      intro fn sel irFn bindings hfn hcompileFn hbind
      simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
        (hSupported := hSupported) hfn tx initialWorld] using
        hfunction fn sel irFn bindings hfn hcompileFn hbind)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld, sourceContractSemantics] using hlegacy

private theorem legacy_function_correct_of_supportedSourceFunctionSemanticsExceptMappingWrites
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    ∀ fn sel irFn bindings,
      fn ∈ selectorDispatchedFunctions model →
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  intro fn sel irFn bindings hfn hcompileFn hbind
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using
    hfunction fn sel irFn bindings hfn hcompileFn hbind

/-- Tier 2 dispatch wrapper for the alternate singleton-storage-write support
witness. This keeps the public theorem surface aligned with the ordinary
`SupportedSpec` path while reusing the existing legacy dispatch skeleton. -/
theorem interpretContract_correct_of_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  simpa [supportedSourceContractSemanticsExceptMappingWrites_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld, sourceContractSemantics] using
    (interpretContract_correct_of_compiled_functions
      (habi := fun _ hfn => (hSupported.supportedFunctionOfSelectorDispatched hfn).standardAbi)
      (model := model)
      (selectors := selectors)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction :=
        legacy_function_correct_of_supportedSourceFunctionSemanticsExceptMappingWrites
          (model := model)
          (selectors := selectors)
          (hSupported := hSupported)
          (tx := tx)
          (initialWorld := initialWorld)
          hfunction))

/-- Helper-aware compiled-side wrapper for the alternate singleton
mapping-write dispatch theorem. This packages the compiled-side retarget as a
single conservative-extension equality for `runtimeContractOfFunctions`. -/
theorem interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hhelperIR :
      interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    interpretContract_correct_of_compiled_functions_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [hhelperIR] using hlegacy

/-- Disjointness-based helper-aware wrapper for the alternate singleton
mapping-write dispatch theorem. -/
theorem interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir_of_disjointRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hdisjointIR :
      DisjointRuntimeContract (runtimeContractOfFunctions model.name irFns)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hhelperIR :=
      interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed
        (runtimeContractOfFunctions model.name irFns)
        hdisjointIR
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Closed helper-aware wrapper for the alternate singleton mapping-write
dispatch theorem. Legacy-compatible external bodies are enough to close the
zero-helper-fuel compiled-side conservative-extension goal. -/
theorem interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir_closed
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (irFns : List IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompiled : List.Forall₂ (fun entry irFn => compileFunctionSpec model.fields model.events
        model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies : ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_except_mapping_writes_and_helper_ir
    model selectors hSupported irFns tx initialWorld hcompiled hparamsSupported hfunction
    (interpretIRWithInternalsZeroConservativeExtensionGoal_closed _
      (runtimeContractOfFunctions_legacyCompatible model.name irFns hlegacyBodies) tx _)

/-- Helper-aware compiled-side wrapper for the dispatch theorem.
This packages the remaining compiled-side retarget work as a single
conservative-extension equality for the runtime contract produced by
`runtimeContractOfFunctions`. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hhelperIR :
      interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    interpretContract_correct_of_compiled_functions_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      hHelperProofs
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [hhelperIR] using hlegacy
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal
    (model : CompilationModel) (selectors : List Nat) (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hcompiled : List.Forall₂ (fun entry irFn => compileFunctionSpec model.fields model.events
        model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies : ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body)
    (hhelperIRGoal : InterpretIRWithInternalsZeroConservativeExtensionGoal
      (runtimeContractOfFunctions model.name irFns)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    model selectors hSupported hHelperProofs irFns tx initialWorld hcompiled hparamsSupported
    hfunction (hhelperIRGoal (runtimeContractOfFunctions_legacyCompatible _ _ hlegacyBodies) tx _)

/-- Disjointness-based helper-aware dispatch wrapper. This drops the stronger
legacy-compatibility runtime assumption in favor of the compiled-side condition
actually needed by `interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint`. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hdisjointIR :
      DisjointRuntimeContract (runtimeContractOfFunctions model.name irFns)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hhelperIR :=
      interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed
        (runtimeContractOfFunctions model.name irFns)
        hdisjointIR
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_closed
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies :
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals (runtimeContractOfFunctions model.name irFns) 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_compiled_functions_with_helper_proofs_and_helper_ir_goal
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (irFns := irFns)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
    (hlegacyBodies := hlegacyBodies)
    (hhelperIRGoal :=
      interpretIRWithInternalsZeroConservativeExtensionGoal_closed
        (runtimeContractOfFunctions model.name irFns))

end Dispatch

end Compiler.Proofs.IRGeneration
