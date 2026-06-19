import Compiler.Proofs.IRGeneration.SourceSemantics

set_option linter.unnecessarySimpa false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace ContractShape

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

/-- `attachNonReentrantGuard` is the identity for lock-free functions, so the
guarded per-function compile in `compileValidatedCore` collapses to the plain
`compileFunctionSpec` mapM on the supported (lock-free) fragment. -/
theorem attachNonReentrantGuard_eq_of_none
    (fields : List Field) (spec : FunctionSpec) (irFn : IRFunction)
    (hnone : spec.nonReentrantLock = none) :
    attachNonReentrantGuard fields spec irFn = Except.ok irFn := by
  simp [attachNonReentrantGuard, hnone, pure, Except.pure]

theorem compileGuardedFunctionSpec_eq_of_none
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef) (internalFunctions : List FunctionSpec)
    (sel : Nat) (fnSpec : FunctionSpec)
    (hnone : fnSpec.nonReentrantLock = none) :
    compileGuardedFunctionSpec fields events errors adtTypes internalFunctions sel fnSpec =
      compileFunctionSpec fields events errors adtTypes sel fnSpec internalFunctions := by
  unfold compileGuardedFunctionSpec
  cases hcomp : compileFunctionSpec fields events errors adtTypes sel fnSpec internalFunctions with
  | error err => simp [bind, Except.bind]
  | ok irFn =>
      simp [bind, Except.bind,
        attachNonReentrantGuard_eq_of_none fields fnSpec irFn hnone]

theorem guardedFunctionsMapM_eq
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (adtTypes : List AdtTypeDef) (internalFunctions : List FunctionSpec) :
    ∀ (entries : List (FunctionSpec × Nat)),
      (∀ e ∈ entries, e.1.nonReentrantLock = none) →
      (entries.mapM fun entry =>
        compileGuardedFunctionSpec fields events errors adtTypes internalFunctions entry.2 entry.1) =
      entries.mapM fun entry =>
        compileFunctionSpec fields events errors adtTypes entry.2 entry.1 internalFunctions
  | [], _ => rfl
  | e :: rest, hnolock => by
      have hhead : e.1.nonReentrantLock = none := hnolock e (by simp)
      have htail := guardedFunctionsMapM_eq fields events errors adtTypes internalFunctions rest
        (fun e' he' => hnolock e' (List.mem_cons_of_mem _ he'))
      simp only [List.mapM_cons,
        compileGuardedFunctionSpec_eq_of_none fields events errors adtTypes internalFunctions e.2 e.1 hhead,
        htail]

theorem supportedSpecExceptMappingWrites_entries_lock_free
    {model : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites model selectors) :
    ∀ e ∈ (model.functions.filter
        (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors,
      (e : FunctionSpec × Nat).1.nonReentrantLock = none := by
  intro e he
  have hmem := (List.of_mem_zip he).1
  exact (hSupported.functions e.1 (List.mem_filter.mp hmem).1).noNonReentrant

theorem supportedSpec_entries_lock_free
    {model : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpec model selectors) :
    ∀ e ∈ (model.functions.filter
        (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors,
      (e : FunctionSpec × Nat).1.nonReentrantLock = none := by
  intro e he
  have hmem := (List.of_mem_zip he).1
  exact (hSupported.functions e.1 (List.mem_filter.mp hmem).1).noNonReentrant

theorem supportedSpecWithScalarEvents_entries_lock_free
    {model : CompilationModel} {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents model selectors) :
    ∀ e ∈ (model.functions.filter
        (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors,
      (e : FunctionSpec × Nat).1.nonReentrantLock = none := by
  intro e he
  have hmem := (List.of_mem_zip he).1
  exact (hSupported.functions e.1 (List.mem_filter.mp hmem).1).noNonReentrant

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
    hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  simp only [guardedFunctionsMapM_eq model.fields [] [] [] [] _
    (supportedSpec_entries_lock_free hSupported)] at hcore
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
    hnoInternalFns, hSupported.noAdtTypes] at hcore
  simp only [bind, Except.bind, pure, Except.pure, List.mapM_nil] at hcore
  simp only [guardedFunctionsMapM_eq model.fields model.events model.errors [] [] _
    (supportedSpec_entries_lock_free hSupported)] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec model.fields model.events model.errors [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor model.fields model.events model.errors [] model.constructor with _ | deployStmts
    · simp [hmap, hctor, pure, Except.pure] at hcore
    · simp [hmap, hctor, pure, Except.pure] at hcore
      cases hcore
      rfl

private theorem compileValidatedCore_ok_yields_deploy_compileConstructor
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    compileConstructor model.fields model.events model.errors [] model.constructor =
      Except.ok ir.deploy := by
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
    hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  simp only [guardedFunctionsMapM_eq model.fields [] [] [] [] _
    (supportedSpec_entries_lock_free hSupported)] at hcore
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
      cases hcore
      simpa [hSupported.noEvents, hSupported.noErrors] using hctor

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
  rw [hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  simp only [guardedFunctionsMapM_eq (applySlotAliasRanges model.fields model.slotAliasRanges)
    model.events model.errors model.adtTypes [] _
    (supportedSpec_entries_lock_free hSupported)] at hcore
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
  rw [hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure] at hcore
  simp only [guardedFunctionsMapM_eq (applySlotAliasRanges model.fields model.slotAliasRanges)
    model.events model.errors model.adtTypes [] _
    (supportedSpec_entries_lock_free hSupported)] at hcore
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

private theorem compileValidatedCore_ok_yields_compiled_functions_with_scalar_events
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    List.Forall₂
      (fun entry irFn =>
        compileFunctionSpec model.fields model.events model.errors [] entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors)
      ir.functions := by
  have hfallback := pickUniqueFunctionByName_eq_ok_none_of_absent
    "fallback" model.functions hSupported.surface.noFallback
  have hreceive := pickUniqueFunctionByName_eq_ok_none_of_absent
    "receive" model.functions hSupported.surface.noReceive
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_all_nonInternal model.functions
      hSupported.noInternalFunctions
  unfold compileValidatedCore at hcore
  rw [hSupported.normalizedFields, hSupported.noAdtTypes, hSupported.noErrors,
    hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, pure, Except.pure] at hcore
  simp only [guardedFunctionsMapM_eq model.fields model.events [] [] [] _
    (supportedSpecWithScalarEvents_entries_lock_free hSupported)] at hcore
  rcases hmap : ((model.functions.filter
      (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
      (fun x => compileFunctionSpec model.fields model.events [] [] x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · simp [hmap] at hcore
    rcases hctor :
        compileConstructor model.fields model.events [] [] model.constructor with _ | deployStmts
    · simp [hctor] at hcore
      cases hcore
    · simp [hctor] at hcore
      have hfunctions : ir.functions = irFns := by
        injection hcore with hir
        cases hir
        rfl
      have hcompiled := compiled_functions_forall₂_of_mapM_ok
        model.fields model.events [] _ _ hmap
      simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
        hfunctions, hSupported.noErrors] using hcompiled

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
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_compiled_functions_with_scalar_events
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

theorem compile_ok_yields_deploy_compileConstructor
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    compileConstructor model.fields model.events model.errors [] model.constructor =
      Except.ok ir.deploy := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simp [hvalidate] at hcompile
    exact compileValidatedCore_ok_yields_deploy_compileConstructor
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

end ContractShape

end Compiler.Proofs.IRGeneration
