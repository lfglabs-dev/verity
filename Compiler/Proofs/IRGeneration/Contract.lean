import Compiler.Proofs.IRGeneration.Dispatch
import Compiler.Proofs.IRGeneration.ContractShape

set_option linter.unnecessarySimpa false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

namespace Contract

private theorem pickUniqueFunctionByName_eq_ok_none_of_absent
    (name : String) (funcs : List FunctionSpec)
    (habsent : ∀ fn ∈ funcs, fn.name != name) :
    pickUniqueFunctionByName name funcs = Except.ok none := by
  induction funcs with
  | nil =>
      rfl
  | cons fn rest ih =>
      have hfn : (fn.name == name) = false := by
        by_cases heq : fn.name = name
        · have habs := habsent fn (by simp)
          simp [heq] at habs
        · simp [heq]
      have hrest : ∀ fn' ∈ rest, fn'.name != name := by
        intro fn' hmem
        exact habsent fn' (by simp [hmem])
      have ih' := ih hrest
      simpa [pickUniqueFunctionByName, hfn] using ih'

private theorem compiled_functions_forall₂_of_mapM_ok
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    ∀ (entries : List (FunctionSpec × Nat)) irFns,
      (entries.mapM fun (entry : FunctionSpec × Nat) =>
        compileFunctionSpec fields events errors [] entry.2 entry.1) = Except.ok irFns →
      List.Forall₂
        (fun (entry : FunctionSpec × Nat) irFn =>
          compileFunctionSpec fields events errors [] entry.2 entry.1 = Except.ok irFn)
        entries irFns := by
  intro entries
  induction entries with
  | nil =>
      intro irFns hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro irFns hmap
      rcases hstep : compileFunctionSpec fields events errors [] entry.2 entry.1 with _ | irFn
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail : List.mapM
            (fun (entry : FunctionSpec × Nat) =>
              compileFunctionSpec fields events errors [] entry.2 entry.1) entries with _ | irFnsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)

private theorem compiled_internal_functions_forall₂_of_mapM_ok
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef) :
    ∀ (entries : List FunctionSpec) internalDefs,
      (entries.mapM (compileInternalFunction fields events errors [])) =
        Except.ok internalDefs →
      List.Forall₂
        (fun fn internalDef =>
          compileInternalFunction fields events errors [] fn = Except.ok internalDef)
        entries internalDefs := by
  intro entries
  induction entries with
  | nil =>
      intro internalDefs hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro internalDefs hmap
      rcases hstep : compileInternalFunction fields events errors [] entry with _ | internalDef
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail :
          List.mapM (compileInternalFunction fields events errors []) entries with _ | internalDefsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)

private theorem exists_right_of_forall₂_mem_left
    {α β : Type}
    {R : α → β → Prop}
    {xs : List α}
    {ys : List β}
    (hrel : List.Forall₂ R xs ys)
    {x : α}
    (hmem : x ∈ xs) :
    ∃ y, y ∈ ys ∧ R x y := by
  induction hrel with
  | nil =>
      cases hmem
  | @cons headX headY tailX tailY hhead htail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact ⟨headY, by simp, hhead⟩
      · rcases ih hmemTail with ⟨y, hy, hRy⟩
        exact ⟨y, by simp [hy], hRy⟩

private theorem filterInternalFunctions_eq_nil_of_all_nonInternal :
    ∀ (fns : List FunctionSpec),
      (∀ fn ∈ fns, fn.isInternal = false) →
        fns.filter (·.isInternal) = []
  | [], _ => rfl
  | fn :: rest, hall => by
      have hfn : fn.isInternal = false := hall fn (by simp)
      have hrest : ∀ fn' ∈ rest, fn'.isInternal = false := by
        intro fn' hmem
        exact hall fn' (by simp [hmem])
      simp [hfn, filterInternalFunctions_eq_nil_of_all_nonInternal rest hrest]

private theorem filterInternalFunctions_eq_nil_of_supported
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    model.functions.filter (·.isInternal) = [] := by
  exact filterInternalFunctions_eq_nil_of_all_nonInternal model.functions
    (hSupported.noInternalFunctions)

private theorem filterInternalFunctions_eq_nil_of_supported_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
    model.functions.filter (·.isInternal) = [] := by
  exact filterInternalFunctions_eq_nil_of_all_nonInternal model.functions
    (hSupported.noInternalFunctions)

private theorem compileValidatedCore_ok_yields_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported model selectors hSupported
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields,
    hSupported.noAdtTypes, hSupported.noEvents, hSupported.noErrors,
    hnoInternalFns, hfallback, hreceive, hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rw [ContractShape.guardedFunctionsMapM_eq model.fields [] [] [] [] _
    (ContractShape.supportedSpec_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields [] [] [] x.2 x.1) with _ | irFns
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
              compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
            ((model.functions.filter
                (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors)
            irFns :=
        by
          simpa [hSupported.noEvents, hSupported.noErrors] using
            (compiled_functions_forall₂_of_mapM_ok model.fields [] [] _ _ hmap)
      simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
        hfunctions] using hcompiled

private theorem compileValidatedCore_ok_yields_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported_except_mapping_writes model selectors hSupported
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields,
    hSupported.noAdtTypes, hSupported.noEvents, hSupported.noErrors,
    hnoInternalFns, hfallback, hreceive, hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rw [ContractShape.guardedFunctionsMapM_eq model.fields [] [] [] [] _
    (ContractShape.supportedSpecExceptMappingWrites_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields [] [] [] x.2 x.1) with _ | irFns
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
              compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
            ((model.functions.filter
                (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors)
            irFns :=
        by
          simpa [hSupported.noEvents, hSupported.noErrors] using
            (compiled_functions_forall₂_of_mapM_ok model.fields [] [] _ _ hmap)
      simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
        hfunctions] using hcompiled

private theorem compileValidatedCore_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported model selectors hSupported
  have harray : contractUsesArrayElement model = false :=
    hSupported.contractUsesArrayElement_eq_false
  have hstorageArray : contractUsesStorageArrayElement model = false :=
    hSupported.contractUsesStorageArrayElement_eq_false
  have hdynamicBytesEq : contractUsesDynamicBytesEq model = false :=
    hSupported.contractUsesDynamicBytesEq_eq_false
  have hmulDiv512 : contractUsesMulDiv512 model = false :=
    hSupported.contractUsesMulDiv512_eq_false
  have hparamDyn : contractUsesParamDynamicHeadWord model = false :=
    hSupported.contractUsesParamDynamicHeadWord_eq_false
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields, hfallback, hreceive,
    contractUsesPlainArrayElement, contractUsesArrayElementWord, harray,
    hstorageArray, hdynamicBytesEq, hmulDiv512, hparamDyn,
    hSupported.noCheckedArithmetic,
    hnoInternalFns, hSupported.noAdtTypes, hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcore
  rw [ContractShape.guardedFunctionsMapM_eq model.fields model.events model.errors [] [] _
    (ContractShape.supportedSpec_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
    · simp [hmap, hctor] at hcore
      cases hcore
    · simp [hmap, hctor] at hcore
      cases hcore
      rfl

private theorem compileValidatedCore_ok_yields_noFallbackEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported model selectors hSupported
  unfold compileValidatedCore at hcore
  rw [hnoInternalFns, hfallback, hreceive, hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  rw [ContractShape.guardedFunctionsMapM_eq (applySlotAliasRanges model.fields model.slotAliasRanges)
    model.events model.errors model.adtTypes [] _
    (ContractShape.supportedSpec_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes model.constructor with _ | deployStmts
    · simp [hmap, hctor, Pure.pure, Except.pure] at hcore
    · simp [hmap, hctor, Pure.pure, Except.pure] at hcore
      cases hcore
      rfl

private theorem compileValidatedCore_ok_yields_noReceiveEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported model selectors hSupported
  unfold compileValidatedCore at hcore
  rw [hnoInternalFns, hfallback, hreceive, hSupported.surface.noTemplateIntrinsics] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  rw [ContractShape.guardedFunctionsMapM_eq (applySlotAliasRanges model.fields model.slotAliasRanges)
    model.events model.errors model.adtTypes [] _
    (ContractShape.supportedSpec_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes model.constructor with _ | deployStmts
    · simp [hmap, hctor, Pure.pure, Except.pure] at hcore
    · simp [hmap, hctor, Pure.pure, Except.pure] at hcore
      cases hcore
      rfl

theorem supported_params_of_supportedSpec
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := by
    exact List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

theorem supported_params_of_supportedSpec_with_scalar_events
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := by
    exact List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

theorem supported_params_of_supportedSpec_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := by
    exact List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

theorem interpretIR_eq_runtimeContractOfFunctions
    (ir : IRContract)
    (runtimeName : String)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialState : IRState)
    (hfunctions : ir.functions = irFns) :
    interpretIR ir tx initialState =
      interpretIR (Dispatch.runtimeContractOfFunctions runtimeName irFns) tx initialState := by
  cases ir
  subst hfunctions
  simp [interpretIR, Dispatch.runtimeContractOfFunctions]

theorem interpretContract_correct_of_ir_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (irFns : List IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hfunctions : ir.functions = irFns)
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
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretIR_eq_runtimeContractOfFunctions
    (ir := ir)
    (runtimeName := model.name)
    (irFns := irFns)
    (tx := tx)
    (initialState := FunctionBody.initialIRStateForTx model tx initialWorld)
    (hfunctions := hfunctions)]
  exact Dispatch.interpretContract_correct_of_compiled_functions
    (model := model) (selectors := selectors) (irFns := irFns)
    (tx := tx) (initialWorld := initialWorld)
    hcompiled hparamsSupported hfunction

theorem compile_preserves_semantics_of_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (_hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions)
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
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact interpretContract_correct_of_ir_functions
    (model := model)
    (selectors := selectors)
    (ir := ir)
    (irFns := ir.functions)
    (tx := tx)
    (initialWorld := initialWorld)
    (hfunctions := rfl)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)

/-- Derive the compiled runtime function table directly from
`CompilationModel.compile = Except.ok ir` and `SupportedSpec`, without any
intermediate `List.Forall₂` hypothesis supplied by callers. -/
theorem compile_ok_yields_compiled_functions
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_compiled_functions_with_scalar_events
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  exact ContractShape.compile_ok_yields_compiled_functions_with_scalar_events
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (ir := ir)
    (hcompile := hcompile)

theorem compile_ok_yields_compiled_functions_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_compiled_functions_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_internalFunctions_nil
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_noFallbackEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_noFallbackEntrypoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_noReceiveEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_noReceiveEntrypoint
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcore := hcompile)

theorem compile_ok_yields_internalFunctions_nil_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported_except_mapping_writes model selectors hSupported
  have harray : contractUsesArrayElement model = false :=
    hSupported.contractUsesArrayElement_eq_false
  have hstorageArray : contractUsesStorageArrayElement model = false :=
    hSupported.contractUsesStorageArrayElement_eq_false
  have hdynamicBytesEq : contractUsesDynamicBytesEq model = false :=
    hSupported.contractUsesDynamicBytesEq_eq_false
  have hmulDiv512 : contractUsesMulDiv512 model = false :=
    hSupported.contractUsesMulDiv512_eq_false
  have hparamDyn : contractUsesParamDynamicHeadWord model = false :=
    hSupported.contractUsesParamDynamicHeadWord_eq_false
  have hcheckedArithmetic : contractUsesCheckedArithmetic model = false :=
    hSupported.noCheckedArithmetic
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    unfold compileValidatedCore at hcompile
    rw [hSupported.normalizedFields, hfallback, hreceive,
      contractUsesPlainArrayElement, contractUsesArrayElementWord, harray,
      hstorageArray, hdynamicBytesEq, hmulDiv512, hparamDyn,
      hcheckedArithmetic,
      hnoInternalFns, hSupported.noAdtTypes, hSupported.surface.noTemplateIntrinsics] at hcompile
    simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcompile
    rw [ContractShape.guardedFunctionsMapM_eq model.fields model.events model.errors [] [] _
      (ContractShape.supportedSpecExceptMappingWrites_entries_lock_free hSupported)] at hcompile
    rcases hmap :
        ((model.functions.filter
            (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
          (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
    · simp [hmap] at hcompile
    · rcases hctor :
          compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
      · simp [hmap, hctor] at hcompile
        cases hcompile
      · simp [hmap, hctor] at hcompile
        injection hcompile with hir
        cases hir
        rfl

theorem compile_ok_yields_noFallbackEntrypoint_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported_except_mapping_writes model selectors hSupported
  have harray : contractUsesArrayElement model = false :=
    hSupported.contractUsesArrayElement_eq_false
  have hstorageArray : contractUsesStorageArrayElement model = false :=
    hSupported.contractUsesStorageArrayElement_eq_false
  have hdynamicBytesEq : contractUsesDynamicBytesEq model = false :=
    hSupported.contractUsesDynamicBytesEq_eq_false
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    unfold compileValidatedCore at hcompile
    rw [hSupported.normalizedFields, hfallback, hreceive,
      contractUsesPlainArrayElement, contractUsesArrayElementWord, harray,
      hstorageArray, hdynamicBytesEq, hnoInternalFns, hSupported.noAdtTypes, hSupported.surface.noTemplateIntrinsics] at hcompile
    simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcompile
    rw [ContractShape.guardedFunctionsMapM_eq model.fields model.events model.errors [] [] _
      (ContractShape.supportedSpecExceptMappingWrites_entries_lock_free hSupported)] at hcompile
    rcases hmap :
        ((model.functions.filter
            (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
          (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
    · simp [hmap] at hcompile
    · rcases hctor :
          compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
      · simp [hmap, hctor] at hcompile
        cases hcompile
      · simp [hmap, hctor] at hcompile
        injection hcompile with hir
        cases hir
        rfl

theorem compile_ok_yields_noReceiveEntrypoint_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hSupported.noFallback
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hSupported.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_supported_except_mapping_writes model selectors hSupported
  have harray : contractUsesArrayElement model = false :=
    hSupported.contractUsesArrayElement_eq_false
  have hstorageArray : contractUsesStorageArrayElement model = false :=
    hSupported.contractUsesStorageArrayElement_eq_false
  have hdynamicBytesEq : contractUsesDynamicBytesEq model = false :=
    hSupported.contractUsesDynamicBytesEq_eq_false
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    unfold compileValidatedCore at hcompile
    rw [hSupported.normalizedFields, hfallback, hreceive,
      contractUsesPlainArrayElement, contractUsesArrayElementWord, harray,
      hstorageArray, hdynamicBytesEq, hnoInternalFns, hSupported.noAdtTypes, hSupported.surface.noTemplateIntrinsics] at hcompile
    simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcompile
    rw [ContractShape.guardedFunctionsMapM_eq model.fields model.events model.errors [] [] _
      (ContractShape.supportedSpecExceptMappingWrites_entries_lock_free hSupported)] at hcompile
    rcases hmap :
        ((model.functions.filter
            (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
          (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
    · simp [hmap] at hcompile
    · rcases hctor :
          compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
      · simp [hmap, hctor] at hcompile
        cases hcompile
      · simp [hmap, hctor] at hcompile
        injection hcompile with hir
        cases hir
        rfl

-- NOTE: compileValidatedCore_ok_yields_supportedRuntimeHelperTableInterface and
-- compile_ok_yields_supportedRuntimeHelperTableInterface are BLOCKED by missing
-- DirectInternalHelperPerCalleeCompileCatalog infrastructure in GenericInduction.lean.
-- They require the helper function interface witness machinery that is not yet implemented.

/-- Generic function-level closure from `SupportedSpec` and successful
`compileFunctionSpec`, with no residual body-level premises such as `hsource`,
`hbodyExec`, or `hmatch`. -/
theorem compileFunctionSpec_correct_generic
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hfnModel : fn ∈ model.functions := List.mem_of_mem_filter hfn
  rcases Function.compileFunctionSpec_ok_components
      model.fields model.events model.errors sel fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  have hcorrect :=
    Function.supported_function_correct
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hvalidateInputs := hvalidateInputs)
    (fn := fn)
    (selector := sel)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (bindings := bindings)
    (hfn := hfn)
    (hvalidate := hvalidate)
    (hreturns := hreturns)
    (hbodyCompile := hbodyCompile)
    (hcompile := by simpa using hcompileFn)
    (hbind := hbind)
    (hcalldataSizeFits := hcalldataSizeFits)
  simpa [supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using hcorrect

/-- Tier 2 generic function-level closure from
`SupportedSpecExceptMappingWrites` and successful `compileFunctionSpec`. This
exposes the widened singleton storage-write fragment on the same public theorem
surface as the ordinary supported-function wrapper. -/
theorem compileFunctionSpec_correct_generic_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcorrect :=
    Function.supported_function_correct_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (selector := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using hcorrect

theorem compileFunctionSpec_correct_generic_except_mapping_writes_stmtSafety
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcorrect :=
    Function.supported_function_correct_except_mapping_writes_stmtSafety
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (selector := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using hcorrect

/-- Helper-proof-carrying function-level generic theorem.
This is the proof-ready theorem surface for the helper-composition step (#1630).
The `hHelperProofs` argument is now backed by a first-class *source-level* reuse
interface: `SourceSemantics.SupportedSpecHelperProofs.helperCallSummarySound` (and
its `eval`/`exec` call-site corollaries) thread the once-proved helper catalog
through to every selector-dispatched caller and call site. This compiled-side
function proof still reduces through the helper-excluding `SupportedStmtList`
fragment, so consuming that reuse interface here — retargeting the body proof —
is the tracked next step; the trusted boundary is unchanged. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rcases Function.compileFunctionSpec_ok_components
      model.fields model.events model.errors sel fn irFn hcompileFn with
    ⟨returns, bodyStmts, hvalidate, hreturns, hbodyCompile, hirFn⟩
  subst hirFn
  exact Function.supported_function_correct_with_helper_proofs
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (hvalidateInputs := hvalidateInputs)
    (fn := fn)
    (selector := sel)
    (returns := returns)
    (bodyStmts := bodyStmts)
    (irFn := Function.compiledFunctionIR sel fn returns bodyStmts)
    (tx := tx)
    (initialWorld := initialWorld)
    (bindings := bindings)
    (hfn := hfn)
    (hvalidate := hvalidate)
    (hreturns := hreturns)
    (hbodyCompile := hbodyCompile)
    (hcompile := by simpa using hcompileFn)
    (hbind := hbind)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)

/-- Helper-aware compiled-side wrapper for the generic function theorem.
This does not strengthen the current proof boundary by itself: it factors the
eventual retarget from `execIRFunction` to `execIRFunctionWithInternals` behind
the exact conservative-extension equality that still remains to be proved on the
compiled side. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hhelperIR :
      execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      execIRFunction irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    compileFunctionSpec_correct_generic_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (hvalidateInputs := hvalidateInputs)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (htxNormalized := htxNormalized)
      (bindings := bindings)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
  simpa [hhelperIR] using hlegacy

/-- Direct helper-aware compiled-side wrapper for the generic function theorem.
This consumes the exact helper-aware body/IR goal and executes the compiled
function through `execIRFunctionWithInternals` directly, leaving only the
generated ABI parameter-load prefix disjointness as an explicit compiled-side
premise. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (Function.compiledFunctionIR sel fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (Function.prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hparamDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract
        (genParamLoads fn.params)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact Function.supported_function_correct_with_helper_proofs_body_goal_with_internals
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract
    fn sel returns bodyStmts irFn tx initialWorld bindings hfn hvalidate hreturns
    hbodyCompile hcompileFn hbind htxNormalized extraFuel hcompiledBodyFuel
    hbodyCorrect hparamDisjoint hcalldataSizeFits

/-- Packaged helper-aware compiled-side wrapper that discharges the ABI
parameter-load prefix disjointness from the runtime contract's internal-table
naming invariant, rather than taking it as an opaque premise. This is the
selector-dispatch consumer seam: once the whole-contract theorem establishes
`InternalTableNamesInternalPrefixed` for the compiled runtime contract, each
per-function correctness obligation feeds straight into
`execIRFunctionWithInternals` without the `genParamLoads` disjointness witness
having to be supplied by hand. Param supportedness comes from `SupportedSpec`. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_internalNamesPrefixed
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (Function.compiledFunctionIR sel fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (Function.prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hinv : InternalTableNamesInternalPrefixed runtimeContract) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract fn sel returns
    bodyStmts irFn tx initialWorld htxNormalized bindings extraFuel hcalldataSizeFits hfn
    hvalidate hreturns hbodyCompile hcompileFn hbind hcompiledBodyFuel hbodyCorrect
    (Function.genParamLoads_callsDisjoint_of_internalNamesPrefixed runtimeContract fn.params
      (supported_params_of_supportedSpec model selectors hSupported fn hfn) hinv)

/-- Reserved-name variant of
`compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_internalNamesPrefixed`.
Takes the *true* `InternalTableNamesReserved` invariant — dischargeable from the
real populated internal table via
`InternalTableNamesReserved_of_helpers_append_compiledInternalTable` — and
discharges the ABI parameter-load prefix disjointness through
`Function.genParamLoads_callsDisjoint_of_reserved`. This is the per-function seam
that lets the whole-contract `WithInternals` dispatch retarget consume a populated
internal table containing non-`internal_` compiler helpers. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_reserved
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (Function.compiledFunctionIR sel fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (Function.prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hinv : InternalTableNamesReserved runtimeContract) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract fn sel returns
    bodyStmts irFn tx initialWorld htxNormalized bindings extraFuel hcalldataSizeFits hfn
    hvalidate hreturns hbodyCompile hcompileFn hbind hcompiledBodyFuel hbodyCorrect
    (Function.genParamLoads_callsDisjoint_of_reserved runtimeContract fn.params
      (supported_params_of_supportedSpec model selectors hSupported fn hfn) hinv)

/-- Whole-contract-facing consumer seam. Rather than taking the runtime
contract's naming invariant `InternalTableNamesInternalPrefixed` as an opaque
premise, this variant derives it from the structural compilation fact that every
statement in the runtime internal table is a `compileInternalFunction` output.
This is the concrete step that threads PR #2117's `WithInternals` selector seam
into the whole-contract dispatch path: once the dispatch proof exhibits the
internal table as compiled internal helpers, the per-function obligation flows
into `execIRFunctionWithInternals` with no hand-supplied disjointness witness and
no `internalFunctions = []` default-empty helper-world assumption. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_compiledInternalTable
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (Function.compiledFunctionIR sel fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (Function.prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel)
    (hcompiledTable : ∀ stmt ∈ runtimeContract.internalFunctions,
        ∃ (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
          (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
          (targetFork : Verity.Core.Intrinsics.HardFork)
          (internalFunctions : List FunctionSpec),
          compileInternalFunction fields events errors adtTypes spec targetFork internalFunctions
            = Except.ok stmt) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_internalNamesPrefixed
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract fn sel returns
    bodyStmts irFn tx initialWorld htxNormalized bindings extraFuel hcalldataSizeFits hfn
    hvalidate hreturns hbodyCompile hcompileFn hbind hcompiledBodyFuel hbodyCorrect
    (Function.InternalTableNamesInternalPrefixed_of_all_compiledInternal runtimeContract
      hcompiledTable)

/-- Generalized `Forall₂` bridge for the internal-function compilation `mapM`.

Unlike `compiled_internal_functions_forall₂_of_mapM_ok` (which fixes
`adtTypes = []` and the default `targetFork`/`internalFunctions` arguments), this
matches the exact call shape used by `compileValidatedCore` when it populates the
`internalFuncDefs` segment of the runtime internal table:
`internalFns.mapM (fun fn => compileInternalFunction fields events errors adtTypes fn targetFork internalFns)`. -/
private theorem compiled_internal_functions_forall₂_of_mapM_ok'
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFns : List FunctionSpec) :
    ∀ (entries : List FunctionSpec) internalDefs,
      (entries.mapM (fun fn =>
        compileInternalFunction fields events errors adtTypes fn targetFork internalFns)) =
        Except.ok internalDefs →
      List.Forall₂
        (fun fn internalDef =>
          compileInternalFunction fields events errors adtTypes fn targetFork internalFns =
            Except.ok internalDef)
        entries internalDefs := by
  intro entries
  induction entries with
  | nil =>
      intro internalDefs hmap
      cases hmap
      simp
  | cons entry entries ih =>
      intro internalDefs hmap
      rcases hstep :
          compileInternalFunction fields events errors adtTypes entry targetFork internalFns with
        _ | internalDef
      · simp only [List.mapM_cons, hstep, bind, Except.bind] at hmap
        cases hmap
      · rcases htail :
          List.mapM (fun fn =>
            compileInternalFunction fields events errors adtTypes fn targetFork internalFns)
            entries with _ | internalDefsTail
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
        · simp only [List.mapM_cons, hstep, htail, bind, Except.bind] at hmap
          cases hmap
          exact List.Forall₂.cons hstep (ih _ htail)

/-- Mirror of `exists_right_of_forall₂_mem_left`: a member of the right list of a
`Forall₂` witnesses a related member on the left. -/
private theorem exists_left_of_forall₂_mem_right
    {α β : Type}
    {R : α → β → Prop}
    {xs : List α}
    {ys : List β}
    (hrel : List.Forall₂ R xs ys)
    {y : β}
    (hmem : y ∈ ys) :
    ∃ x, x ∈ xs ∧ R x y := by
  induction hrel with
  | nil =>
      cases hmem
  | @cons headX headY tailX tailY hhead htail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmemTail
      · exact ⟨headX, by simp, hhead⟩
      · rcases ih hmemTail with ⟨x, hx, hRx⟩
        exact ⟨x, by simp [hx], hRx⟩

/-- Whole-contract legacy-compatibility bridge for a concrete `compileValidatedCore`
output.  Given the per-statement compiled legacy-compatibility interface
(`StmtListCompiledLegacyCompatible`) for every selector-dispatched function body,
the emitted runtime contract's external bodies all stay inside the
legacy-compatible external Yul subset (`LegacyCompatibleExternalBodies`).

This reduces the `LegacyCompatibleExternalBodies` premise still carried by the
helper-aware whole-contract retarget theorem
(`compile_preserves_semantics_with_helper_proofs_and_helper_ir_of_compileValidatedCore`)
to the same per-statement legacy obligations that #2080 already tracks for the
disjoint interface, closing the whole-contract plumbing for the body-shape half. -/
theorem legacyCompatibleExternalBodies_of_compileValidatedCore_of_interface
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir)
    (hbodies :
      ∀ entry ∈ SourceSemantics.selectorFunctionPairs model selectors,
        StmtListCompiledLegacyCompatible model.fields
          (entry.1.params.map (·.name)) entry.1.body) :
    LegacyCompatibleExternalBodies ir := by
  have hforall₂ :=
    compileValidatedCore_ok_yields_compiled_functions model selectors hSupported ir hcore
  intro fn hfn
  obtain ⟨⟨spec, sel⟩, hentry, hcompileEntry⟩ :=
    exists_left_of_forall₂_mem_right hforall₂ hfn
  have hfnDispatched : spec ∈ selectorDispatchedFunctions model := by
    simpa [SourceSemantics.selectorFunctionPairs] using (List.of_mem_zip hentry).1
  have hparams : ∀ param ∈ spec.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec model selectors hSupported spec hfnDispatched
  have hcompileEntry' :
      compileFunctionSpec model.fields [] [] [] sel spec = Except.ok fn := by
    rw [← hSupported.noEvents, ← hSupported.noErrors]
    exact hcompileEntry
  exact Function.compileFunctionSpec_body_legacyCompatible_of_interface
    model.fields sel spec fn hparams (hbodies (spec, sel) hentry) hcompileEntry'

/-- Structural compiled-internal-table premise, derived from the compilation
pipeline's `mapM` step. Every statement produced by
`internalFns.mapM compileInternalFunction` is a `compileInternalFunction` output
in the exact existential shape consumed by
`..._of_body_goal_of_compiledInternalTable`'s `hcompiledTable`. This is
non-vacuous: it holds for a *non-empty* `internalFns`, so it does not depend on
any `internalFunctions = []` default-empty helper-world assumption. -/
theorem compileInternalFunction_mapM_mem_exists
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFns : List FunctionSpec)
    (internalDefs : List YulStmt)
    (hmap : internalFns.mapM (fun fn =>
        compileInternalFunction fields events errors adtTypes fn targetFork internalFns) =
        Except.ok internalDefs) :
    ∀ stmt ∈ internalDefs,
      ∃ (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
        (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
        (targetFork : Verity.Core.Intrinsics.HardFork)
        (internalFunctions : List FunctionSpec),
        compileInternalFunction fields events errors adtTypes spec targetFork internalFunctions =
          Except.ok stmt := by
  intro stmt hstmt
  have hforall₂ :=
    compiled_internal_functions_forall₂_of_mapM_ok'
      fields events errors adtTypes targetFork internalFns internalFns internalDefs hmap
  obtain ⟨fn, _hfn, hcompile⟩ := exists_left_of_forall₂_mem_right hforall₂ hstmt
  exact ⟨fields, events, errors, adtTypes, fn, targetFork, internalFns, hcompile⟩

/-- Consumer seam packaging: for a runtime contract whose internal table *is* the
`compileInternalFunction` image of some internal-function list, discharge the
`hcompiledTable` premise of
`compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_compiledInternalTable`
directly from the compilation pipeline's `mapM` equation — no hand-supplied
`InternalTableNamesInternalPrefixed` witness and no `internalFunctions = []`
default-empty assumption. -/
theorem compiledInternalTable_of_internalFunctions_eq_mapM
    (runtimeContract : IRContract)
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFns : List FunctionSpec)
    (internalDefs : List YulStmt)
    (hmap : internalFns.mapM (fun fn =>
        compileInternalFunction fields events errors adtTypes fn targetFork internalFns) =
        Except.ok internalDefs)
    (hinternal : runtimeContract.internalFunctions = internalDefs) :
    ∀ stmt ∈ runtimeContract.internalFunctions,
      ∃ (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
        (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
        (targetFork : Verity.Core.Intrinsics.HardFork)
        (internalFunctions : List FunctionSpec),
        compileInternalFunction fields events errors adtTypes spec targetFork internalFunctions =
          Except.ok stmt := by
  rw [hinternal]
  exact compileInternalFunction_mapM_mem_exists fields events errors adtTypes targetFork
    internalFns internalDefs hmap

/-- Structural distribution of the reserved-name invariant over a segmented
table. `compileValidatedCore` populates `internalFunctions` as
`<prebuilt helper segments> ++ internalFuncDefs` (see `compileValidatedCore` in
`Compiler/CompilationModel/Dispatch.lean`), so the whole-table
`InternalTableNamesReserved` obligation is exactly the conjunction of the same
invariant restricted to each segment. Proving it via `List.mem_append` avoids any
dependence on `filterMap`-append rewriting and keeps the two segment obligations
independent, which is what lets a caller discharge the helper segment and the
`internalFuncDefs` segment by different routes. -/
theorem InternalTableNamesReserved_of_internalFunctions_append
    (contract : IRContract)
    (helpers internalDefs : List YulStmt)
    (hcontract : contract.internalFunctions = helpers ++ internalDefs)
    (hhelpers : ∀ d ∈ helpers.filterMap irInternalFunctionDefOfStmt?,
        IsReservedInternalHelperName d.name)
    (hinternal : ∀ d ∈ internalDefs.filterMap irInternalFunctionDefOfStmt?,
        IsReservedInternalHelperName d.name) :
    InternalTableNamesReserved contract := by
  intro d hd
  rw [hcontract, List.mem_filterMap] at hd
  obtain ⟨stmt, hstmt, hdecode⟩ := hd
  rw [List.mem_append] at hstmt
  rcases hstmt with hstmt | hstmt
  · exact hhelpers d (List.mem_filterMap.mpr ⟨stmt, hstmt, hdecode⟩)
  · exact hinternal d (List.mem_filterMap.mpr ⟨stmt, hstmt, hdecode⟩)

/-- Consumer seam for the *populated* internal table produced by the compilation
pipeline. A runtime contract whose internal table is a prebuilt helper segment
followed by the `compileInternalFunction` image of some internal-function list
(`runtimeContract.internalFunctions = helpers ++ internalDefs` with
`internalDefs` the `mapM` output) satisfies `InternalTableNamesReserved` as soon
as the helper segment is reserved: the `internalFuncDefs` segment is discharged
structurally from the pipeline's `mapM` equation via
`compileInternalFunction_mapM_mem_exists` +
`Function.InternalTableNamesInternalPrefixed_of_all_compiledInternal` +
`InternalTableNamesReserved_of_internalPrefixed`, and the two segments are
combined by `InternalTableNamesReserved_of_internalFunctions_append`.

This replaces the false `internal_`-prefix helper-segment premise of the previous
slice: real compiler helpers (`__verity_*`, `checked_*`, `panic_error_*`,
template intrinsics) are reserved but *not* `internal_`-prefixed, so the helper
premise here is dischargeable from the actual populated table. It feeds the
reserved-name naming invariant consumed by
`compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_reserved`
without any `internalFunctions = []` default-empty assumption. -/
theorem InternalTableNamesReserved_of_helpers_append_compiledInternalTable
    (runtimeContract : IRContract)
    (helpers : List YulStmt)
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFns : List FunctionSpec)
    (internalDefs : List YulStmt)
    (hmap : internalFns.mapM (fun fn =>
        compileInternalFunction fields events errors adtTypes fn targetFork internalFns) =
        Except.ok internalDefs)
    (hcontract : runtimeContract.internalFunctions = helpers ++ internalDefs)
    (hhelpers : ∀ d ∈ helpers.filterMap irInternalFunctionDefOfStmt?,
        IsReservedInternalHelperName d.name) :
    InternalTableNamesReserved runtimeContract := by
  refine InternalTableNamesReserved_of_internalFunctions_append
    runtimeContract helpers internalDefs hcontract hhelpers ?_
  have hcompiled :=
    compileInternalFunction_mapM_mem_exists fields events errors adtTypes targetFork
      internalFns internalDefs hmap
  exact InternalTableNamesReserved_of_internalPrefixed
    { runtimeContract with internalFunctions := internalDefs }
    (Function.InternalTableNamesInternalPrefixed_of_all_compiledInternal
      { runtimeContract with internalFunctions := internalDefs } hcompiled)

/-- Segment-local reserved-name invariant for a list of internal helper
statements. This is the helper-list analogue of `InternalTableNamesReserved`,
used to compose the concrete helper segments emitted by `compileValidatedCore`
before they are appended to the compiled source-internal definitions. -/
def DecodedInternalHelperNamesReserved (stmts : List YulStmt) : Prop :=
  ∀ d ∈ stmts.filterMap irInternalFunctionDefOfStmt?,
    IsReservedInternalHelperName d.name

private theorem DecodedInternalHelperNamesReserved.nil :
    DecodedInternalHelperNamesReserved [] := by
  intro d hd
  cases hd

private theorem DecodedInternalHelperNamesReserved.append
    {xs ys : List YulStmt}
    (hxs : DecodedInternalHelperNamesReserved xs)
    (hys : DecodedInternalHelperNamesReserved ys) :
    DecodedInternalHelperNamesReserved (xs ++ ys) := by
  intro d hd
  rw [List.filterMap_append, List.mem_append] at hd
  rcases hd with hd | hd
  · exact hxs d hd
  · exact hys d hd

private theorem DecodedInternalHelperNamesReserved.ifList
    (b : Bool) {xs : List YulStmt}
    (hxs : DecodedInternalHelperNamesReserved xs) :
    DecodedInternalHelperNamesReserved (if b then xs else []) := by
  cases b
  · exact DecodedInternalHelperNamesReserved.nil
  · exact hxs

private theorem DecodedInternalHelperNamesReserved.of_funcDefNames
    {stmts : List YulStmt}
    (hnames : ∀ name ∈ stmts.filterMap yulFuncDefName?,
      IsReservedInternalHelperName name) :
    DecodedInternalHelperNamesReserved stmts := by
  intro d hd
  rw [List.mem_filterMap] at hd
  obtain ⟨stmt, hstmt, hdecode⟩ := hd
  exact hnames d.name (List.mem_filterMap.mpr ⟨stmt, hstmt, by
    cases stmt <;> simp [irInternalFunctionDefOfStmt?, yulFuncDefName?] at hdecode ⊢
    cases hdecode
    rfl⟩)

private theorem IsReservedInternalHelperName.templateHelperName (name : String) :
    IsReservedInternalHelperName
      (Verity.Core.Intrinsics.YulLowering.templateHelperName name) := by
  refine ⟨"__verity_", by simp [reservedInternalHelperPrefixes], ?_⟩
  unfold Verity.Core.Intrinsics.YulLowering.templateHelperName
  simp only [String.data_append]
  rw [List.append_assoc]
  rw [List.take_append_of_le_length
    (l₁ := (toString "__verity_intrinsic_template_").data)
    (l₂ := ((toString name).data ++ (toString "").data))
    (i := "__verity_".data.length)
    (by decide)]
  decide

private theorem DecodedInternalHelperNamesReserved.templateFuncDef
    (name : String) (lowering : Verity.Core.Intrinsics.YulLowering)
    (stmt : YulStmt)
    (hstmt :
      Verity.Core.Intrinsics.YulLowering.templateFuncDef? name lowering =
        some stmt) :
    DecodedInternalHelperNamesReserved [stmt] := by
  intro d hd
  cases lowering <;> simp [Verity.Core.Intrinsics.YulLowering.templateFuncDef?] at hstmt
  subst stmt
  simp [irInternalFunctionDefOfStmt?] at hd
  rcases hd with rfl
  exact IsReservedInternalHelperName.templateHelperName name

private theorem templateIntrinsicHelper_mapM_reserved :
    ∀ (items : List (String × Verity.Core.Intrinsics.YulLowering)) helpers,
      items.mapM (fun (name, lowering) =>
        match Verity.Core.Intrinsics.YulLowering.templateFuncDef? name lowering with
        | some funcDef => pure funcDef
        | none =>
            Except.error s!"Compilation error: intrinsic {name} is not a template lowering") =
          Except.ok helpers →
      DecodedInternalHelperNamesReserved helpers
  | [], helpers, hmap => by
      cases hmap
      exact DecodedInternalHelperNamesReserved.nil
  | (name, lowering) :: items, helpers, hmap => by
      rcases hfunc :
          Verity.Core.Intrinsics.YulLowering.templateFuncDef? name lowering with _ | stmt
      · simp [List.mapM_cons, hfunc] at hmap
        cases hmap
      · rcases htail :
          items.mapM (fun (name, lowering) =>
            match Verity.Core.Intrinsics.YulLowering.templateFuncDef? name lowering with
            | some funcDef => pure funcDef
            | none =>
                Except.error s!"Compilation error: intrinsic {name} is not a template lowering")
            with _ | tail
        · simp [List.mapM_cons, hfunc, htail] at hmap
        · simp [List.mapM_cons, hfunc, htail] at hmap
          cases hmap
          exact DecodedInternalHelperNamesReserved.append
            (DecodedInternalHelperNamesReserved.templateFuncDef name lowering stmt hfunc)
            (templateIntrinsicHelper_mapM_reserved items tail htail)

private theorem compileTemplateIntrinsicHelpers_reserved
    (spec : CompilationModel)
    (helpers : List YulStmt)
    (hcompile : compileTemplateIntrinsicHelpers spec = Except.ok helpers) :
    DecodedInternalHelperNamesReserved helpers := by
  unfold compileTemplateIntrinsicHelpers at hcompile
  rcases hitems : dedupTemplateIntrinsics (templateIntrinsicItems spec) with _ | items
  · simp [hitems] at hcompile
    cases hcompile
  · simp [hitems] at hcompile
    exact templateIntrinsicHelper_mapM_reserved items helpers hcompile

private theorem DecodedInternalHelperNamesReserved.arrayElementBase :
    DecodedInternalHelperNamesReserved
      [ checkedArrayElementCalldataHelper
      , checkedArrayElementMemoryHelper
      ] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [checkedArrayElementCalldataHelperName, checkedArrayElementMemoryHelperName] at hname
  rcases hname with rfl | rfl <;> decide)

private theorem DecodedInternalHelperNamesReserved.arrayElementWord :
    DecodedInternalHelperNamesReserved
      [ checkedArrayElementWordCalldataHelper
      , checkedArrayElementWordMemoryHelper
      , checkedArrayElementDynamicWordCalldataHelper
      , checkedArrayElementDynamicWordMemoryHelper
      , checkedArrayElementDynamicDataOffsetCalldataHelper
      , checkedArrayElementDynamicDataOffsetMemoryHelper
      , checkedArrayElementDynamicMemberLengthCalldataHelper
      , checkedArrayElementDynamicMemberLengthMemoryHelper
      , checkedArrayElementDynamicMemberDataOffsetCalldataHelper
      , checkedArrayElementDynamicMemberDataOffsetMemoryHelper
      , checkedArrayElementDynamicMemberElementCalldataHelper
      , checkedArrayElementDynamicMemberElementMemoryHelper
      ] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [checkedArrayElementWordCalldataHelperName, checkedArrayElementWordMemoryHelperName,
    checkedArrayElementDynamicWordCalldataHelperName,
    checkedArrayElementDynamicWordMemoryHelperName,
    checkedArrayElementDynamicDataOffsetCalldataHelperName,
    checkedArrayElementDynamicDataOffsetMemoryHelperName,
    checkedArrayElementDynamicMemberLengthCalldataHelperName,
    checkedArrayElementDynamicMemberLengthMemoryHelperName,
    checkedArrayElementDynamicMemberDataOffsetCalldataHelperName,
    checkedArrayElementDynamicMemberDataOffsetMemoryHelperName,
    checkedArrayElementDynamicMemberElementCalldataHelperName,
    checkedArrayElementDynamicMemberElementMemoryHelperName] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide)

private theorem DecodedInternalHelperNamesReserved.paramDynamicHeadWord :
    DecodedInternalHelperNamesReserved
      [ checkedParamDynamicHeadWordCalldataHelper
      , checkedParamDynamicHeadWordMemoryHelper
      , checkedParamDynamicMemberLengthCalldataHelper
      , checkedParamDynamicMemberLengthMemoryHelper
      , checkedParamDynamicMemberDataOffsetCalldataHelper
      , checkedParamDynamicMemberDataOffsetMemoryHelper
      , checkedParamDynamicMemberElementCalldataHelper
      , checkedParamDynamicMemberElementMemoryHelper
      ] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [checkedParamDynamicHeadWordCalldataHelperName, checkedParamDynamicHeadWordMemoryHelperName,
    checkedParamDynamicMemberLengthCalldataHelperName,
    checkedParamDynamicMemberLengthMemoryHelperName,
    checkedParamDynamicMemberDataOffsetCalldataHelperName,
    checkedParamDynamicMemberDataOffsetMemoryHelperName,
    checkedParamDynamicMemberElementCalldataHelperName,
    checkedParamDynamicMemberElementMemoryHelperName] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

private theorem DecodedInternalHelperNamesReserved.mulDiv512 :
    DecodedInternalHelperNamesReserved
      [ fullMulDivHelper
      , fullMulDivUpHelper
      ] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [fullMulDivHelperName, fullMulDivUpHelperName] at hname
  rcases hname with rfl | rfl <;> decide)

private theorem DecodedInternalHelperNamesReserved.storageArray :
    DecodedInternalHelperNamesReserved [checkedStorageArrayElementHelper] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [checkedStorageArrayElementHelperName] at hname
  rcases hname with rfl
  decide)

private theorem DecodedInternalHelperNamesReserved.dynamicBytesEq :
    DecodedInternalHelperNamesReserved
      [dynamicBytesEqCalldataHelper, dynamicBytesEqMemoryHelper] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [dynamicBytesEqCalldataHelperName, dynamicBytesEqMemoryHelperName] at hname
  rcases hname with rfl | rfl <;> decide)

private theorem DecodedInternalHelperNamesReserved.checkedArithmetic :
    DecodedInternalHelperNamesReserved
      [ panicError0x11Helper
      , panicError0x12Helper
      , checkedAddUint256Helper
      , checkedSubUint256Helper
      , checkedMulUint256Helper
      , checkedDivUint256Helper
      ] :=
  DecodedInternalHelperNamesReserved.of_funcDefNames (by
  intro name hname
  simp [panicError0x11HelperName, panicError0x12HelperName,
    checkedAddUint256HelperName, checkedSubUint256HelperName,
    checkedMulUint256HelperName, checkedDivUint256HelperName] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

private theorem DecodedInternalHelperNamesReserved.compileValidatedCore_helpers
    (arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired : Bool)
    (templateIntrinsicHelpers : List YulStmt)
    (htemplate : DecodedInternalHelperNamesReserved templateIntrinsicHelpers) :
    DecodedInternalHelperNamesReserved
      (((if arrayHelpersRequired then
          [ checkedArrayElementCalldataHelper
          , checkedArrayElementMemoryHelper
          ]
        else
          []) ++
        (if arrayElementWordHelpersRequired then
          [ checkedArrayElementWordCalldataHelper
          , checkedArrayElementWordMemoryHelper
          , checkedArrayElementDynamicWordCalldataHelper
          , checkedArrayElementDynamicWordMemoryHelper
          , checkedArrayElementDynamicDataOffsetCalldataHelper
          , checkedArrayElementDynamicDataOffsetMemoryHelper
          , checkedArrayElementDynamicMemberLengthCalldataHelper
          , checkedArrayElementDynamicMemberLengthMemoryHelper
          , checkedArrayElementDynamicMemberDataOffsetCalldataHelper
          , checkedArrayElementDynamicMemberDataOffsetMemoryHelper
          , checkedArrayElementDynamicMemberElementCalldataHelper
          , checkedArrayElementDynamicMemberElementMemoryHelper
          ]
        else
          []) ++
        (if paramDynamicHeadWordHelpersRequired then
          [ checkedParamDynamicHeadWordCalldataHelper
          , checkedParamDynamicHeadWordMemoryHelper
          , checkedParamDynamicMemberLengthCalldataHelper
          , checkedParamDynamicMemberLengthMemoryHelper
          , checkedParamDynamicMemberDataOffsetCalldataHelper
          , checkedParamDynamicMemberDataOffsetMemoryHelper
          , checkedParamDynamicMemberElementCalldataHelper
          , checkedParamDynamicMemberElementMemoryHelper
          ]
        else
          []) ++
        (if mulDiv512HelpersRequired then
          [ fullMulDivHelper
          , fullMulDivUpHelper
          ]
        else
          [])) ++
      (if storageArrayHelpersRequired then
        [checkedStorageArrayElementHelper]
      else
        []) ++
      (if dynamicBytesEqHelpersRequired then
        [dynamicBytesEqCalldataHelper, dynamicBytesEqMemoryHelper]
      else
        []) ++
      (if checkedArithmeticHelpersRequired then
        [ panicError0x11Helper
        , panicError0x12Helper
        , checkedAddUint256Helper
        , checkedSubUint256Helper
        , checkedMulUint256Helper
        , checkedDivUint256Helper
        ]
      else
        []) ++
      templateIntrinsicHelpers) :=
  by
  simpa [List.append_assoc] using
  DecodedInternalHelperNamesReserved.append
    (DecodedInternalHelperNamesReserved.append
      (DecodedInternalHelperNamesReserved.append
        (DecodedInternalHelperNamesReserved.append
          (DecodedInternalHelperNamesReserved.append
            (DecodedInternalHelperNamesReserved.ifList arrayHelpersRequired
              DecodedInternalHelperNamesReserved.arrayElementBase)
            (DecodedInternalHelperNamesReserved.ifList arrayElementWordHelpersRequired
              DecodedInternalHelperNamesReserved.arrayElementWord))
          (DecodedInternalHelperNamesReserved.ifList paramDynamicHeadWordHelpersRequired
            DecodedInternalHelperNamesReserved.paramDynamicHeadWord))
        (DecodedInternalHelperNamesReserved.ifList mulDiv512HelpersRequired
          DecodedInternalHelperNamesReserved.mulDiv512))
      (DecodedInternalHelperNamesReserved.ifList storageArrayHelpersRequired
        DecodedInternalHelperNamesReserved.storageArray))
    (DecodedInternalHelperNamesReserved.append
      (DecodedInternalHelperNamesReserved.ifList dynamicBytesEqHelpersRequired
        DecodedInternalHelperNamesReserved.dynamicBytesEq)
      (DecodedInternalHelperNamesReserved.append
        (DecodedInternalHelperNamesReserved.ifList checkedArithmeticHelpersRequired
          DecodedInternalHelperNamesReserved.checkedArithmetic)
        htemplate))

def compileValidatedCoreHelperSegment
    (arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired : Bool)
    (templateIntrinsicHelpers : List YulStmt) : List YulStmt :=
  (((if arrayHelpersRequired then
      [ checkedArrayElementCalldataHelper
      , checkedArrayElementMemoryHelper
      ]
    else
      []) ++
    (if arrayElementWordHelpersRequired then
      [ checkedArrayElementWordCalldataHelper
      , checkedArrayElementWordMemoryHelper
      , checkedArrayElementDynamicWordCalldataHelper
      , checkedArrayElementDynamicWordMemoryHelper
      , checkedArrayElementDynamicDataOffsetCalldataHelper
      , checkedArrayElementDynamicDataOffsetMemoryHelper
      , checkedArrayElementDynamicMemberLengthCalldataHelper
      , checkedArrayElementDynamicMemberLengthMemoryHelper
      , checkedArrayElementDynamicMemberDataOffsetCalldataHelper
      , checkedArrayElementDynamicMemberDataOffsetMemoryHelper
      , checkedArrayElementDynamicMemberElementCalldataHelper
      , checkedArrayElementDynamicMemberElementMemoryHelper
      ]
    else
      []) ++
    (if paramDynamicHeadWordHelpersRequired then
      [ checkedParamDynamicHeadWordCalldataHelper
      , checkedParamDynamicHeadWordMemoryHelper
      , checkedParamDynamicMemberLengthCalldataHelper
      , checkedParamDynamicMemberLengthMemoryHelper
      , checkedParamDynamicMemberDataOffsetCalldataHelper
      , checkedParamDynamicMemberDataOffsetMemoryHelper
      , checkedParamDynamicMemberElementCalldataHelper
      , checkedParamDynamicMemberElementMemoryHelper
      ]
    else
      []) ++
    (if mulDiv512HelpersRequired then
      [ fullMulDivHelper
      , fullMulDivUpHelper
      ]
    else
      [])) ++
  (if storageArrayHelpersRequired then
    [checkedStorageArrayElementHelper]
  else
    []) ++
  (if dynamicBytesEqHelpersRequired then
    [dynamicBytesEqCalldataHelper, dynamicBytesEqMemoryHelper]
  else
    []) ++
  (if checkedArithmeticHelpersRequired then
    [ panicError0x11Helper
    , panicError0x12Helper
    , checkedAddUint256Helper
    , checkedSubUint256Helper
    , checkedMulUint256Helper
    , checkedDivUint256Helper
    ]
  else
    []) ++
  templateIntrinsicHelpers)

/-- Populated-table connector for the exact prebuilt helper segment shape emitted
by `compileValidatedCore`. It removes the caller-supplied helper-segment
reserved-name premise from
`InternalTableNamesReserved_of_helpers_append_compiledInternalTable`; callers now
only provide the template-helper compilation equation and the already-existing
compiled source-internal `mapM` equation. -/
theorem InternalTableNamesReserved_of_compileValidatedCore_helpers_append_compiledInternalTable
    (runtimeContract : IRContract)
    (arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired : Bool)
    (templateIntrinsicHelpers : List YulStmt)
    (htemplate : DecodedInternalHelperNamesReserved templateIntrinsicHelpers)
    (fields : List Field)
    (events : List EventDef)
    (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef)
    (targetFork : Verity.Core.Intrinsics.HardFork)
    (internalFns : List FunctionSpec)
    (internalDefs : List YulStmt)
    (hmap : internalFns.mapM (fun fn =>
        compileInternalFunction fields events errors adtTypes fn targetFork internalFns) =
        Except.ok internalDefs)
    (hcontract : runtimeContract.internalFunctions =
      compileValidatedCoreHelperSegment
        arrayHelpersRequired arrayElementWordHelpersRequired
        paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
        storageArrayHelpersRequired dynamicBytesEqHelpersRequired
        checkedArithmeticHelpersRequired templateIntrinsicHelpers ++ internalDefs) :
    InternalTableNamesReserved runtimeContract := by
  refine InternalTableNamesReserved_of_helpers_append_compiledInternalTable
    runtimeContract
    (compileValidatedCoreHelperSegment
      arrayHelpersRequired arrayElementWordHelpersRequired
      paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
      storageArrayHelpersRequired dynamicBytesEqHelpersRequired
      checkedArithmeticHelpersRequired templateIntrinsicHelpers)
    fields events errors adtTypes targetFork internalFns internalDefs hmap ?_ ?_
  · simpa [List.append_assoc] using hcontract
  · intro d hd
    have hhelpers : DecodedInternalHelperNamesReserved
        (compileValidatedCoreHelperSegment
          arrayHelpersRequired arrayElementWordHelpersRequired
          paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
          storageArrayHelpersRequired dynamicBytesEqHelpersRequired
          checkedArithmeticHelpersRequired templateIntrinsicHelpers) := by
      simpa [compileValidatedCoreHelperSegment, List.append_assoc] using
        (DecodedInternalHelperNamesReserved.compileValidatedCore_helpers
          arrayHelpersRequired arrayElementWordHelpersRequired
          paramDynamicHeadWordHelpersRequired mulDiv512HelpersRequired
          storageArrayHelpersRequired dynamicBytesEqHelpersRequired
          checkedArithmeticHelpersRequired templateIntrinsicHelpers htemplate)
    exact hhelpers d hd

/-- Full table-shape connector for the concrete `compileValidatedCore` output.

The previous connector packaged the exact helper segment but still required
callers to thread the template-helper reservation proof, the compiled-internal
`mapM` equation, and the final `internalFunctions` append equation separately.
This theorem extracts all three facts from
`compileValidatedCore model selectors = Except.ok runtimeContract` and packages
the real populated table:

`compileValidatedCoreHelperSegment ... templateIntrinsicHelpers ++ internalFuncDefs`.

It is intentionally independent of `SupportedSpec`: the supported fragment may
make the compiled internal segment empty today, but this connector follows the
pipeline shape directly and remains non-vacuous for source-internal functions. -/
theorem InternalTableNamesReserved_of_compileValidatedCore
    (model : CompilationModel)
    (selectors : List Nat)
    (runtimeContract : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok runtimeContract) :
    InternalTableNamesReserved runtimeContract := by
  unfold compileValidatedCore at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  rcases hfallback :
      pickUniqueFunctionByName "fallback" model.functions with _ | fallbackSpec
  · simp [hfallback] at hcore
  · rcases hreceive :
        pickUniqueFunctionByName "receive" model.functions with _ | receiveSpec
    · simp [hfallback, hreceive] at hcore
    · rcases hfunctions :
          (((model.functions.filter fun fn => !fn.isInternal && !isInteropEntrypointName fn.name).zip
              selectors).mapM fun entry =>
            compileGuardedFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
              model.events model.errors model.adtTypes (model.functions.filter (·.isInternal))
              entry.2 entry.1) with _ | functions
      · simp [hfallback, hreceive, hfunctions] at hcore
      · rcases hinternalDefs :
            ((model.functions.filter (·.isInternal)).mapM fun fn =>
              compileInternalFunction (applySlotAliasRanges model.fields model.slotAliasRanges)
                model.events model.errors model.adtTypes fn (targetFork := .cancun)
                (model.functions.filter (·.isInternal))) with _ | internalDefs
        · simp [hfallback, hreceive, hfunctions, hinternalDefs] at hcore
        · rcases htemplate :
              (if (templateIntrinsicItems model).isEmpty then
                pure []
              else
                compileTemplateIntrinsicHelpers model) with _ | templateIntrinsicHelpers
          · by_cases hitems : (templateIntrinsicItems model).isEmpty
            · simp [hitems] at htemplate
              cases htemplate
            · simp [hitems] at htemplate
              simp [hfallback, hreceive, hfunctions, hinternalDefs, hitems, htemplate] at hcore
          · simp [hfallback, hreceive, hfunctions, hinternalDefs] at hcore
            by_cases hitems : (templateIntrinsicItems model).isEmpty
            · simp [hitems] at htemplate
              cases htemplate
              simp [hitems] at hcore
              rcases hfallbackEntrypoint :
                  fallbackSpec.mapM
                    (compileSpecialEntrypoint
                      (applySlotAliasRanges model.fields model.slotAliasRanges)
                      model.events model.errors model.adtTypes (targetFork := .cancun)
                      (model.functions.filter (·.isInternal))) with _ | fallbackEntrypoint
              · simp [hfallbackEntrypoint] at hcore
              · rcases hreceiveEntrypoint :
                    receiveSpec.mapM
                      (compileSpecialEntrypoint
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes (targetFork := .cancun)
                        (model.functions.filter (·.isInternal))) with _ | receiveEntrypoint
                · simp [hfallbackEntrypoint, hreceiveEntrypoint] at hcore
                · rcases hdeploy :
                      compileConstructor
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes model.constructor
                        (targetFork := .cancun) (model.functions.filter (·.isInternal)) with
                    _ | deploy
                  · simp [hfallbackEntrypoint, hreceiveEntrypoint, hdeploy] at hcore
                  · simp [hfallbackEntrypoint, hreceiveEntrypoint, hdeploy] at hcore
                    have hcontract :
                        runtimeContract.internalFunctions =
                          compileValidatedCoreHelperSegment
                            (contractUsesPlainArrayElement model)
                            (contractUsesArrayElementWord model)
                            (contractUsesParamDynamicHeadWord model)
                            (contractUsesMulDiv512 model)
                            (contractUsesStorageArrayElement model)
                            (contractUsesDynamicBytesEq model)
                            (contractUsesCheckedArithmetic model)
                            [] ++ internalDefs := by
                      rw [← hcore]
                      simp [compileValidatedCoreHelperSegment, List.append_assoc]
                    exact
                      InternalTableNamesReserved_of_compileValidatedCore_helpers_append_compiledInternalTable
                        runtimeContract
                        (contractUsesPlainArrayElement model)
                        (contractUsesArrayElementWord model)
                        (contractUsesParamDynamicHeadWord model)
                        (contractUsesMulDiv512 model)
                        (contractUsesStorageArrayElement model)
                        (contractUsesDynamicBytesEq model)
                        (contractUsesCheckedArithmetic model)
                        [] DecodedInternalHelperNamesReserved.nil
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes
                        Verity.Core.Intrinsics.HardFork.cancun
                        (model.functions.filter (·.isInternal))
                        internalDefs hinternalDefs hcontract
            · simp [hitems] at htemplate
              simp [hitems, htemplate] at hcore
              rcases hfallbackEntrypoint :
                  fallbackSpec.mapM
                    (compileSpecialEntrypoint
                      (applySlotAliasRanges model.fields model.slotAliasRanges)
                      model.events model.errors model.adtTypes (targetFork := .cancun)
                      (model.functions.filter (·.isInternal))) with _ | fallbackEntrypoint
              · simp [hfallbackEntrypoint] at hcore
              · rcases hreceiveEntrypoint :
                    receiveSpec.mapM
                      (compileSpecialEntrypoint
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes (targetFork := .cancun)
                        (model.functions.filter (·.isInternal))) with _ | receiveEntrypoint
                · simp [hfallbackEntrypoint, hreceiveEntrypoint] at hcore
                · rcases hdeploy :
                      compileConstructor
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes model.constructor
                        (targetFork := .cancun) (model.functions.filter (·.isInternal)) with
                    _ | deploy
                  · simp [hfallbackEntrypoint, hreceiveEntrypoint, hdeploy] at hcore
                  · simp [hfallbackEntrypoint, hreceiveEntrypoint, hdeploy] at hcore
                    have htemplateReserved :
                        DecodedInternalHelperNamesReserved templateIntrinsicHelpers :=
                      compileTemplateIntrinsicHelpers_reserved model templateIntrinsicHelpers htemplate
                    have hcontract :
                        runtimeContract.internalFunctions =
                          compileValidatedCoreHelperSegment
                            (contractUsesPlainArrayElement model)
                            (contractUsesArrayElementWord model)
                            (contractUsesParamDynamicHeadWord model)
                            (contractUsesMulDiv512 model)
                            (contractUsesStorageArrayElement model)
                            (contractUsesDynamicBytesEq model)
                            (contractUsesCheckedArithmetic model)
                            templateIntrinsicHelpers ++ internalDefs := by
                      rw [← hcore]
                      simp [compileValidatedCoreHelperSegment, List.append_assoc]
                    exact
                      InternalTableNamesReserved_of_compileValidatedCore_helpers_append_compiledInternalTable
                        runtimeContract
                        (contractUsesPlainArrayElement model)
                        (contractUsesArrayElementWord model)
                        (contractUsesParamDynamicHeadWord model)
                        (contractUsesMulDiv512 model)
                        (contractUsesStorageArrayElement model)
                        (contractUsesDynamicBytesEq model)
                        (contractUsesCheckedArithmetic model)
                        templateIntrinsicHelpers htemplateReserved
                        (applySlotAliasRanges model.fields model.slotAliasRanges)
                        model.events model.errors model.adtTypes
                        Verity.Core.Intrinsics.HardFork.cancun
                        (model.functions.filter (·.isInternal))
                        internalDefs hinternalDefs hcontract

/-- Pipeline connector for the current `SupportedSpec` world: a contract produced
by `compileValidatedCore` discharges the structural `hcompiledTable` premise
outright. Under `SupportedSpec` the runtime internal table is empty
(`compileValidatedCore_ok_yields_internalFunctions_nil`), so the premise holds
vacuously; this exhibits the seam being fed from the real compilation output
rather than from a separately-assumed hypothesis. The non-vacuous machinery for a
populated table lives in `compiledInternalTable_of_internalFunctions_eq_mapM`. -/
theorem compiledInternalTable_of_compileValidatedCore
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ∀ stmt ∈ ir.internalFunctions,
      ∃ (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
        (adtTypes : List AdtTypeDef) (spec : FunctionSpec)
        (targetFork : Verity.Core.Intrinsics.HardFork)
        (internalFunctions : List FunctionSpec),
        compileInternalFunction fields events errors adtTypes spec targetFork internalFunctions =
          Except.ok stmt := by
  intro stmt hstmt
  have hnil :=
    compileValidatedCore_ok_yields_internalFunctions_nil model selectors hSupported ir hcore
  rw [hnil] at hstmt
  cases hstmt

/-- Concrete compiled-runtime legacy-compatibility connector.

For the current `SupportedSpec` core pipeline, `compileValidatedCore` still emits
an empty internal table (`compileValidatedCore_ok_yields_internalFunctions_nil`).
Package that concrete output fact with the external-body compatibility witness in
the shape consumed by the closed helper-aware whole-contract theorem. -/
theorem legacyCompatibleRuntimeContract_of_compileValidatedCore
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir)
    (hlegacyBodies : LegacyCompatibleExternalBodies ir) :
    LegacyCompatibleRuntimeContract ir := by
  have hinternal :=
    compileValidatedCore_ok_yields_internalFunctions_nil
      model selectors hSupported ir hcore
  exact ⟨hinternal, hlegacyBodies⟩

/-- Whole-contract dispatch consumer of the compiled-internal-table seam.

This feeds `..._of_body_goal_of_compiledInternalTable`'s `hcompiledTable` premise
directly from the real compilation pipeline output
(`compileValidatedCore model selectors = Except.ok runtimeContract`) via
`compiledInternalTable_of_compileValidatedCore`, rather than requiring the caller
to hand-supply that structural premise. The runtime contract whose
`execIRFunctionWithInternals` dispatch is proven correct is exactly the contract
emitted by the compiler, so the internal-table naming invariant is discharged by
the pipeline itself and no `internalFunctions = []` default-empty assumption is
introduced at the call site. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_compileValidatedCore
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok runtimeContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (returns : List ParamType)
    (bodyStmts : List YulStmt)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (extraFuel : Nat)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hvalidate : validateFunctionSpec fn = Except.ok ())
    (hreturns : functionReturns fn = Except.ok returns)
    (hbodyCompile :
      compileStmtList model.fields model.events model.errors .calldata [] false
        (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hcompiledBodyFuel :
      (genParamLoads fn.params ++ bodyStmts).length + extraFuel =
        sizeOf (Function.compiledFunctionIR sel fn returns bodyStmts).body)
    (hbodyCorrect :
      SupportedFunctionBodyWithHelpersAndHelperIRPreservationGoal
        runtimeContract model fn bodyStmts hSupported.helperFuel tx initialWorld
        (ParamLoading.applyBindingsToIRState
          (Function.prebindRawArgs
            (FunctionBody.initialIRStateForTx model tx initialWorld) fn.params)
          bindings)
        bindings extraFuel) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_body_goal_of_reserved
    model selectors hSupported hHelperProofs hvalidateInputs runtimeContract fn sel returns
    bodyStmts irFn tx initialWorld htxNormalized bindings extraFuel hcalldataSizeFits hfn
    hvalidate hreturns hbodyCompile hcompileFn hbind hcompiledBodyFuel hbodyCorrect
    (InternalTableNamesReserved_of_compileValidatedCore model selectors runtimeContract hcore)

/-- Structured helper-aware compiled-side wrapper for the generic function
theorem. This replaces the raw function-level conservative-extension equality
premise by the compiled-body disjointness witness that proves it. -/
theorem compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir_of_bodyCallsDisjoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (runtimeContract : IRContract)
    (fn : FunctionSpec)
    (sel : Nat)
    (irFn : IRFunction)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (bindings : List (String × Nat))
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfn : fn ∈ selectorDispatchedFunctions model)
    (hcompileFn :
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn)
    (hbind : SourceSemantics.bindSupportedParams fn.params tx.args = some bindings)
    (hbodyDisjoint :
      YulStmtListCallsDisjointFromInternalTable runtimeContract irFn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceFunctionSemantics model selectors hSupported fn tx initialWorld)
      (execIRFunctionWithInternals runtimeContract 0 irFn tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compileFunctionSpec_correct_generic_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (hvalidateInputs := hvalidateInputs)
    (runtimeContract := runtimeContract)
    (fn := fn)
    (sel := sel)
    (irFn := irFn)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (bindings := bindings)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hfn := hfn)
    (hcompileFn := hcompileFn)
    (hbind := hbind)
    (hhelperIR :=
      execIRFunctionWithInternals_eq_execIRFunction_of_bodyCallsDisjoint
        runtimeContract
        irFn
        tx.args
        (FunctionBody.initialIRStateForTx model tx initialWorld)
        hbodyDisjoint)

-- NOTE: ~1174 lines of SORRY'D dead code removed here.  They were 16 commented-out
-- helper-composition theorem sketches (escalating from DirectInternalHelper…Surface
-- through PerCallee…CompileCatalog, RuntimeWitnessCatalog, SemanticKernelCatalog)
-- plus an alternative proof body.  All were blocked by missing
-- DirectInternalHelperPerCalleeCompileCatalog infrastructure.  See git history for
-- the original sketches.
/-- Primary whole-contract Layer 2 theorem: compilation preserves semantics
for any supported `CompilationModel`. No contract-specific bridge premise.
Layer 2 itself is axiom-free; the remaining documented project axiom is the
mapping-slot range assumption tracked in `AXIOMS.md`. -/
theorem compile_preserves_semantics
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
    unfold CompilationModel.compile at hcompile
    simp only [bind, Except.bind] at hcompile
    rcases hvalidate : validateCompileInputs model selectors with _ | validated
    · simp [hvalidate] at hcompile
    · simpa using hvalidate
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec model selectors hSupported
  have hfunction :
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
      (compileFunctionSpec_correct_generic
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hvalidateInputs := hvalidateInputs)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind))
  have hcontract :=
    compile_preserves_semantics_of_compiled_functions
      (model := model)
      (selectors := selectors)
      (ir := ir)
      (tx := tx)
      (initialWorld := initialWorld)
      (_hcompile := hcompile)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hcontract

private theorem scalar_events_contract_function_callback
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeNonEventStepInterface
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint { ir with internalFunctions := [] }
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    ∀ fn sel irFn bindings,
      fn ∈ selectorDispatchedFunctions model →
      compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.interpretFunction model fn tx initialWorld)
        (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  intro fn sel irFn bindings hfn hcompileFn hbind
  simpa [supportedSourceFunctionSemanticsWithScalarEvents_eq_interpretFunction_of_selectorDispatched
    (hSupported := hSupported) hfn tx initialWorld] using
    (Function.compileFunctionSpec_correct_with_scalar_events
      (runtimeContract := { ir with internalFunctions := [] })
      (model := model) (selectors := selectors) (hSupported := hSupported)
      (fn := fn) (sel := sel) (irFn := irFn) (tx := tx)
      (initialWorld := initialWorld) (htxNormalized := htxNormalized)
      (bindings := bindings) (hcalldataSizeFits := hcalldataSizeFits)
      (hfn := hfn) (hcompileFn := hcompileFn) (hbind := hbind)
      (hfuelPos := hfuelPos) (hhelperFree := hhelperFree fn hfn)
      (hstmtDisjoint := hstmtDisjoint fn hfn) (hinternal := rfl))

/-- Whole-contract scalar-event bridge. The scalar-event function theorem is
instantiated with a proof-only runtime contract whose internal helper table is
empty; its conclusion is the plain `execIRFunction` result consumed by the
dispatcher theorem. -/
theorem compile_preserves_semantics_with_scalar_events
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hfuelPos : 0 < hSupported.helperFuel)
    (hhelperFree :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeNonEventStepInterface
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body)
    (hstmtDisjoint :
      ∀ fn, fn ∈ selectorDispatchedFunctions model →
        StmtListHelperFreeCompiledCallsDisjoint { ir with internalFunctions := [] }
          (SourceSemantics.effectiveFields model) (fn.params.map (·.name)) fn.body) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsWithScalarEvents model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled := compile_ok_yields_compiled_functions_with_scalar_events
    (model := model) (selectors := selectors) (hSupported := hSupported)
    (ir := ir) (hcompile := hcompile)
  have hparamsSupported :=
    supported_params_of_supportedSpec_with_scalar_events model selectors hSupported
  have hfunction := scalar_events_contract_function_callback
    model selectors hSupported ir tx initialWorld htxNormalized hcalldataSizeFits
    hfuelPos hhelperFree hstmtDisjoint
  have hcontract := compile_preserves_semantics_of_compiled_functions
    (model := model) (selectors := selectors) (ir := ir) (tx := tx)
    (initialWorld := initialWorld) (_hcompile := hcompile)
    (hcompiled := hcompiled) (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)
  simpa [supportedSourceContractSemanticsWithScalarEvents_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hcontract

/-- Whole-contract Tier 2 bridge for specs whose selector-dispatched bodies use
the alternate singleton-storage-write state interface. This keeps the contract
proof on the same generic dispatch skeleton while widening only the function
correctness theorem it instantiates. -/
theorem compile_preserves_semantics_except_mapping_writes
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety : SupportedStmtListMappingWriteSlotSafety model.fields)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec_except_mapping_writes model selectors hSupported
  have hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact compileFunctionSpec_correct_generic_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
  exact Dispatch.interpretContract_correct_of_compiled_functions_except_mapping_writes
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (irFns := ir.functions)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)

theorem compile_preserves_semantics_except_mapping_writes_stmtSafety
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions_except_mapping_writes
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec_except_mapping_writes model selectors hSupported
  have hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileFunctionSpec model.fields model.events model.errors [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (supportedSourceFunctionSemanticsExceptMappingWrites model selectors hSupported fn tx initialWorld)
          (execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
    intro fn sel irFn bindings hfn hcompileFn hbind
    exact compileFunctionSpec_correct_generic_except_mapping_writes_stmtSafety
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (fn := fn)
      (sel := sel)
      (irFn := irFn)
      (tx := tx)
      (initialWorld := initialWorld)
      (bindings := bindings)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety fn hfn)
      (hfn := hfn)
      (hcompileFn := hcompileFn)
      (hbind := hbind)
  exact Dispatch.interpretContract_correct_of_compiled_functions_except_mapping_writes
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (irFns := ir.functions)
    (tx := tx)
    (initialWorld := initialWorld)
    (hcompiled := hcompiled)
    (hparamsSupported := hparamsSupported)
    (hfunction := hfunction)

/-- Helper-aware compiled-side wrapper for the alternate singleton
mapping-write whole-contract theorem. This keeps the widened Tier 2 theorem
available on `interpretIRWithInternals` while the compiled-side retarget is
factored behind a conservative-extension equality. -/
theorem compile_preserves_semantics_except_mapping_writes_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites model selectors)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hnoConflict : firstFieldWriteSlotConflict model.fields = none)
    (hsafety :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ stmt ∈ fn.body, StmtMappingWriteSlotSafe model.fields stmt)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hhelperIR :
      interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemanticsExceptMappingWrites model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    compile_preserves_semantics_except_mapping_writes_stmtSafety
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (tx := tx)
      (initialWorld := initialWorld)
      (hnoConflict := hnoConflict)
      (hsafety := hsafety)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompile := hcompile)
  simpa [hhelperIR] using hlegacy

/-- Helper-proof-carrying whole-contract Layer 2 theorem.
This theorem family is the stable public interface for the helper-composition
step tracked by `#1630`. Callers pass explicit summary-soundness evidence
(`hHelperProofs`), which is now reusable across callers through the source-level
interface `SourceSemantics.SupportedSpecHelperProofs.helperCallSummarySound` (and
its `eval`/`exec` call-site corollaries): one helper proof in the shared catalog
discharges every call site of every selector-dispatched function. This
whole-contract proof still reduces through the helper-closed path on the compiled
side, so retargeting the body proof to consume that reuse is the remaining step;
the trusted boundary is unchanged. -/
theorem compile_preserves_semantics_with_helper_proofs
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIR ir tx (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hvalidateInputs : validateCompileInputs model selectors = Except.ok () := by
    unfold CompilationModel.compile at hcompile
    simp only [bind, Except.bind] at hcompile
    rcases hvalidate : validateCompileInputs model selectors with _ | validated
    · simp [hvalidate] at hcompile
    · simpa using hvalidate
  have hcompiled :
      List.Forall₂
        (fun entry irFn =>
          compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
        (SourceSemantics.selectorFunctionPairs model selectors)
        ir.functions :=
    compile_ok_yields_compiled_functions
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (ir := ir)
      (hcompile := hcompile)
  have hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
    supported_params_of_supportedSpec model selectors hSupported
  have hfunction :
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
      (compileFunctionSpec_correct_generic_with_helper_proofs
        (model := model)
        (selectors := selectors)
        (hSupported := hSupported)
        (hHelperProofs := hHelperProofs)
        (hvalidateInputs := hvalidateInputs)
        (fn := fn)
        (sel := sel)
        (irFn := irFn)
        (tx := tx)
        (initialWorld := initialWorld)
        (htxNormalized := htxNormalized)
        (bindings := bindings)
        (hcalldataSizeFits := hcalldataSizeFits)
        (hfn := hfn)
        (hcompileFn := hcompileFn)
        (hbind := hbind))
  have hcontract :=
    compile_preserves_semantics_of_compiled_functions
      (model := model)
      (selectors := selectors)
      (ir := ir)
      (tx := tx)
      (initialWorld := initialWorld)
      (_hcompile := hcompile)
      (hcompiled := hcompiled)
      (hparamsSupported := hparamsSupported)
      (hfunction := hfunction)
  simpa [supportedSourceContractSemantics_eq_sourceContractSemantics
    (hSupported := hSupported) tx initialWorld] using hcontract

/-- Helper-aware compiled-side wrapper for the whole-contract theorem.
The remaining compiled-side blocker is exactly the conservative-extension proof
that supplies `hhelperIR`; once that theorem is available, the public Layer 2
contract theorem can retarget to `interpretIRWithInternals` without another
interface change in `Contract.lean`. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hhelperIR :
      interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld) =
      interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hlegacy :=
    compile_preserves_semantics_with_helper_proofs
      (model := model)
      (selectors := selectors)
      (hSupported := hSupported)
      (hHelperProofs := hHelperProofs)
      (ir := ir)
      (tx := tx)
      (initialWorld := initialWorld)
      (htxNormalized := htxNormalized)
      (hcalldataSizeFits := hcalldataSizeFits)
      (hcompile := hcompile)
  simpa [hhelperIR] using hlegacy

/-- Structured helper-aware whole-contract wrapper.
This consumes the named compiled-side conservative-extension target together
with its explicit runtime-contract compatibility witness, instead of requiring
callers to restate the resulting equality manually. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hlegacyIR : LegacyCompatibleRuntimeContract ir)
    (hhelperIRGoal :
      InterpretIRWithInternalsZeroConservativeExtensionGoal ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hhelperIR := hhelperIRGoal
      hlegacyIR
      tx
      (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Disjointness-based helper-aware whole-contract wrapper.
This replaces the legacy-compatible runtime assumption with the weaker
`DisjointRuntimeContract` boundary that future helper-table compilation should
still satisfy even after `ir.internalFunctions` stops being empty. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_of_disjointRuntimeContract
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hdisjointIR : DisjointRuntimeContract ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hhelperIR :=
      interpretIRWithInternalsZeroConservativeExtensionGoalOfDisjoint_closed ir
        hdisjointIR
        tx
        (FunctionBody.initialIRStateForTx model tx initialWorld))

/-- Whole-contract helper-aware retarget connector for a concrete
`compileValidatedCore` output.

This is the validated-core variant of
`compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed`: the
manual `hhelperIR` equality is replaced by the closed helper-aware interpreter
path for the actual runtime contract emitted by `compileValidatedCore`, and the
public `CompilationModel.compile` equality is rebuilt from the validated-input
proof plus the core result. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_of_compileValidatedCore
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hvalidateInputs : validateCompileInputs model selectors = Except.ok ())
    (hcore : compileValidatedCore model selectors = Except.ok ir)
    (hlegacyBodies : LegacyCompatibleExternalBodies ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompile : CompilationModel.compile model selectors = Except.ok ir := by
    unfold CompilationModel.compile
    rw [hvalidateInputs]
    simp only [bind, Except.bind]
    exact hcore
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hlegacyIR :=
      legacyCompatibleRuntimeContract_of_compileValidatedCore
        model selectors hSupported ir hcore hlegacyBodies)
    (hhelperIRGoal := interpretIRWithInternalsZeroConservativeExtensionGoal_closed ir)

/-- Direct helper-aware whole-contract theorem on the current legacy-compatible
runtime-contract boundary. The helper-aware compiled-side conservative-extension
goal is now closed in `IRInterpreter.lean`, so theorem users no longer need to
thread it as an extra hypothesis. -/
theorem compile_preserves_semantics_with_helper_proofs_and_helper_ir_closed
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (hHelperProofs : SourceSemantics.SupportedSpecHelperProofs model selectors hSupported)
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hlegacyIR : LegacyCompatibleRuntimeContract ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics model selectors hSupported tx initialWorld)
      (interpretIRWithInternals ir 0 tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  exact compile_preserves_semantics_with_helper_proofs_and_helper_ir_goal
    (model := model)
    (selectors := selectors)
    (hSupported := hSupported)
    (hHelperProofs := hHelperProofs)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)
    (hlegacyIR := hlegacyIR)
    (hhelperIRGoal := interpretIRWithInternalsZeroConservativeExtensionGoal_closed ir)

/-- First direct consumer of the generic Layer 2 theorem surface: the existing
supported single-function demo model can now obtain whole-contract correctness
by instantiating `compile_preserves_semantics`, with no contract-specific body
bridge premise. -/
theorem counter_supported_spec_compile_preserves_semantics
    (ir : IRContract)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (htxNormalized : Function.TxContextNormalized tx)
    (hcalldataSizeFits : Function.TxCalldataSizeFitsEvm tx)
    (hcompile :
      CompilationModel.compile counterSupportedSpecModel [0xa87d942c] = Except.ok ir) :
    FunctionBody.sourceResultMatchesIRResult
      (supportedSourceContractSemantics
        counterSupportedSpecModel [0xa87d942c] counter_supported_spec tx initialWorld)
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx counterSupportedSpecModel tx initialWorld)) := by
  exact compile_preserves_semantics
    (model := counterSupportedSpecModel)
    (selectors := [0xa87d942c])
    (hSupported := counter_supported_spec)
    (ir := ir)
    (tx := tx)
    (initialWorld := initialWorld)
    (htxNormalized := htxNormalized)
    (hcalldataSizeFits := hcalldataSizeFits)
    (hcompile := hcompile)

end Contract

end Compiler.Proofs.IRGeneration
