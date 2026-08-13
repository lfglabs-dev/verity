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

theorem interpretContract_correct_of_compiled_functions
    (model : CompilationModel)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
  interpretContract_correct_of_functions_generic
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    model selectors irFns tx initialWorld
    (fun fn sel irFn hP => by
      obtain ⟨hp, hs, hpay⟩ := Function.compileFunctionSpec_ok_metadata_with_internals
        model.fields model.events model.errors sel fn irFn [] hP
      exact ⟨hp, hs, hpay⟩)
    hcompiled hparamsSupported hfunction

theorem interpretContractWithInternals_correct_of_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (runtimeContract : IRContract)
    (irFuelSlack : Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : runtimeContract.functions = irFns)
    (hcompiled :
      List.Forall₂
        (fun entry irFn => compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
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
  have hinterp :
      interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      match irFns.find? (fun irFn => irFn.selector == tx.functionSelector) with
      | some irFn =>
          if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
            { success := false
              returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
          else if irFn.params.length ≤ tx.args.length then
            execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
              (FunctionBody.initialIRStateForTx model tx initialWorld)
          else
            { success := false
              returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
      | none =>
          { success := false
            returnValue := none
            finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            finalMappings := Compiler.Proofs.storageAsMappings
              (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events } := by
        simp [interpretIRWithInternals, hfunctions, FunctionBody.initialIRStateForTx]
        congr
  rw [interpretContract_eq_interpretContractWith]
  exact interpretContractWith_correct_generic
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (fun fn => SourceSemantics.interpretFunction model fn tx initialWorld)
    (fun irFn => execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld))
    model selectors irFns tx initialWorld _
    (fun fn sel irFn hP => by
      obtain ⟨hp, hs, hpay⟩ := Function.compileFunctionSpec_ok_metadata_with_internals
        model.fields model.events model.errors sel fn irFn [] hP
      exact ⟨hp, hs, hpay⟩)
    (fun fn hmem hbindNone => interpretFunction_eq_reverted_of_bind_none
      model fn tx initialWorld (hparamsSupported fn hmem) hbindNone)
    hcompiled hparamsSupported hinterp hfunction

/-- Helper-aware dispatch skeleton.  This is the populated-runtime analogue of
`interpretContractWithInternals_correct_of_compiled_functions`, but it keeps
`interpretContractWithHelpers`/`interpretFunctionWithHelpers` all the way
through and therefore does not reduce helper callers to legacy semantics. -/
theorem interpretContractWithHelpersWithInternals_correct_of_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (helperFuel : Nat)
    (runtimeContract : IRContract)
    (irFuelSlack : Nat)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : runtimeContract.functions = irFns)
    (hcompiled :
      List.Forall₂
        (fun entry irFn => compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1
          (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
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
  have hinterp :
      interpretIRWithInternals runtimeContract irFuelSlack tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      match irFns.find? (fun irFn => irFn.selector == tx.functionSelector) with
      | some irFn =>
          if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
            { success := false
              returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
          else if irFn.params.length ≤ tx.args.length then
            execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
              (FunctionBody.initialIRStateForTx model tx initialWorld)
          else
            { success := false
              returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
      | none =>
          { success := false
            returnValue := none
            finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            finalMappings := Compiler.Proofs.storageAsMappings
              (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events } := by
        simp [interpretIRWithInternals, hfunctions, FunctionBody.initialIRStateForTx]
        congr
  rw [interpretContractWithHelpers_eq_interpretContractWith]
  exact interpretContractWith_correct_generic
    (fun fn sel irFn =>
      compileFunctionSpec model.fields model.events model.errors [] sel fn
        (internalFunctions := model.functions.filter (·.isInternal)) = Except.ok irFn)
    (fun fn => SourceSemantics.interpretFunctionWithHelpers model helperFuel fn tx initialWorld)
    (fun irFn => execIRFunctionWithInternals runtimeContract irFuelSlack irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld))
    model selectors irFns tx initialWorld _
    (fun fn sel irFn hP => by
      obtain ⟨hp, hs, hpay⟩ := Function.compileFunctionSpec_ok_metadata_with_internals
        model.fields model.events model.errors sel fn irFn
        (model.functions.filter (·.isInternal)) hP
      exact ⟨hp, hs, hpay⟩)
    (fun fn hmem hbindNone => interpretFunctionWithHelpers_eq_reverted_of_bind_none
      model helperFuel fn tx initialWorld (hparamsSupported fn hmem) hbindNone)
    hcompiled hparamsSupported hinterp hfunction

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
    model selectors hSupported.helperFuel runtimeContract irFuelSlack irFns tx initialWorld
    hfunctions hcompiled (fun fn hfn => hSupported.selectorFunctionParamsSupported hfn) (by
      intro fn sel irFn bindings hfn hcompile hbind
      simpa [supportedSourceFunctionSemanticsWithHelpers] using
        hfunction fn sel irFn bindings hfn hcompile hbind)

/-- Helper-proof-carrying wrapper for the dispatch theorem.
The current proof still reduces helper-aware source semantics to the legacy
helper-free semantics via the helper-excluding `SupportedStmtList` body
fragment, so the additional helper proof slot is present to stabilize the
theorem boundary rather than to widen the proved fragment today. -/
theorem interpretContract_correct_of_compiled_functions_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (_hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacyFunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
      (hSupported := hSupported) hfn tx initialWorld] using
      hfunction fn sel irFn bindings hfn hcompileFn hbind
  have hlegacy :=
    interpretContract_correct_of_compiled_functions
      (model := model)
      (selectors := selectors)
      (irFns := irFns)
      (tx := tx)
      (initialWorld := initialWorld)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hlegacyFunction)
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
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
    model selectors runtimeContract irFuelSlack irFns tx initialWorld hfunctions
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies :
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body) :
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
      interpretIRWithInternalsZeroConservativeExtensionGoal_closed
        (runtimeContractOfFunctions model.name irFns)
        (runtimeContractOfFunctions_legacyCompatible model.name irFns hlegacyBodies)
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))

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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)))
    (hlegacyBodies :
      ∀ irFn ∈ irFns, LegacyCompatibleExternalStmtList irFn.body)
    (hhelperIRGoal :
      InterpretIRWithInternalsZeroConservativeExtensionGoal
        (runtimeContractOfFunctions model.name irFns)) :
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
      hhelperIRGoal
        (runtimeContractOfFunctions_legacyCompatible model.name irFns hlegacyBodies)
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Disjointness-based helper-aware dispatch wrapper.
This drops the stronger legacy-compatibility runtime assumption in favor of the
compiled-side condition actually needed by
`interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint`. -/
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
