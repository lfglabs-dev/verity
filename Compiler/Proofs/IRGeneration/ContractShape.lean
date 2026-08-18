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
      compileFunctionSpec fields events errors adtTypes sel fnSpec
        (targetFork := .cancun) internalFunctions := by
  unfold compileGuardedFunctionSpec
  cases hcomp : compileFunctionSpec fields events errors adtTypes sel fnSpec
      (targetFork := .cancun) internalFunctions with
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
        compileFunctionSpec fields events errors adtTypes entry.2 entry.1
          (targetFork := .cancun) internalFunctions
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

/-- Closed form of the helper `internalFunctions` emitted by
`compileValidatedCore` when the model has no source internal functions and
no template intrinsics: only the usage-gated builtin helper groups remain. -/
def coreHelperInternalFunctions (model : CompilationModel) :
    List Compiler.Yul.YulStmt :=
  ((if contractUsesPlainArrayElement model then
      [ checkedArrayElementCalldataHelper
      , checkedArrayElementMemoryHelper
      ]
    else
      []) ++
    (if contractUsesArrayElementWord model then
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
    (if contractUsesParamDynamicHeadWord model then
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
    (if contractUsesMulDiv512 model then
      [ fullMulDivHelper
      , fullMulDivUpHelper
      ]
    else
      [])) ++
  (if contractUsesStorageArrayElement model then
    [checkedStorageArrayElementHelper, checkedFixedUint128ArrayElementHelper,
      checkedTransientFixedUint128ArrayElementHelper]
  else
    []) ++
  (if contractUsesDynamicBytesEq model then
    [dynamicBytesEqCalldataHelper, dynamicBytesEqMemoryHelper]
  else
    []) ++
  (if contractUsesCheckedArithmetic model then
    [ panicError0x11Helper
    , panicError0x12Helper
    , checkedAddUint256Helper
    , checkedSubUint256Helper
    , checkedMulUint256Helper
    , checkedDivUint256Helper
    ]
  else
    [])

/-- The gated helper groups vanish when no gate fires. -/
theorem coreHelperInternalFunctions_eq_nil
    (model : CompilationModel)
    (harray : contractUsesArrayElement model = false)
    (hstorageArray : contractUsesStorageArrayElement model = false)
    (hdynamicBytesEq : contractUsesDynamicBytesEq model = false)
    (hmulDiv512 : contractUsesMulDiv512 model = false)
    (hparamDyn : contractUsesParamDynamicHeadWord model = false)
    (hcheckedArith : contractUsesCheckedArithmetic model = false) :
    coreHelperInternalFunctions model = [] := by
  unfold coreHelperInternalFunctions contractUsesPlainArrayElement
    contractUsesArrayElementWord
  simp [harray, hstorageArray, hdynamicBytesEq, hmulDiv512, hparamDyn,
    hcheckedArith]

/-- Successful `compile` factors through `compileValidatedCore`. -/
theorem compile_ok_yields_core
    (model : CompilationModel) (selectors : List Nat) (ir : IRContract)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir) :
    compileValidatedCore model selectors = Except.ok ir := by
  unfold CompilationModel.compile at hcompile
  simp only [bind, Except.bind] at hcompile
  rcases hvalidate : validateCompileInputs model selectors with _ | validated
  · simp [hvalidate] at hcompile
  · simpa [hvalidate] using hcompile

/-- Master inversion for `compileValidatedCore` on the lock-free,
no-internal-function, no-template-intrinsic surface: pins every field of the
output contract.  All per-projection shape lemmas derive from this. -/
theorem compileValidatedCore_ok_inv
    (model : CompilationModel) (selectors : List Nat) (ir : IRContract)
    (hfallbackAbsent : ∀ fn ∈ model.functions, fn.name != "fallback")
    (hreceiveAbsent : ∀ fn ∈ model.functions, fn.name != "receive")
    (hnoInternal : ∀ fn ∈ model.functions, fn.isInternal = false)
    (hlockfree : ∀ e ∈ (model.functions.filter
        (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors,
      (e : FunctionSpec × Nat).1.nonReentrantLock = none)
    (hnoTemplate : templateIntrinsicItems model = [])
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ∃ irFns deployStmts,
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) = Except.ok irFns ∧
      compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
        model.events model.errors model.adtTypes model.constructor = Except.ok deployStmts ∧
      ir = { name := model.name
             deploy := deployStmts
             constructorPayable := (model.constructor.map (·.isPayable)).getD false
             functions := irFns
             fallbackEntrypoint := none
             receiveEntrypoint := none
             usesMapping := usesMapping (applySlotAliasRanges model.fields model.slotAliasRanges)
             internalFunctions := coreHelperInternalFunctions model } := by
  have hfallback :
      pickUniqueFunctionByName "fallback" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "fallback" model.functions hfallbackAbsent
  have hreceive :
      pickUniqueFunctionByName "receive" model.functions = Except.ok none :=
    pickUniqueFunctionByName_eq_ok_none_of_absent
      "receive" model.functions hreceiveAbsent
  have hnoInternalFns :
      model.functions.filter (·.isInternal) = [] :=
    filterInternalFunctions_eq_nil_of_all_nonInternal model.functions hnoInternal
  have hnoTemplateEmpty : (templateIntrinsicItems model).isEmpty = true := by
    simp [hnoTemplate]
  unfold compileValidatedCore at hcore
  rw [hnoInternalFns, hfallback, hreceive] at hcore
  simp only [bind, Except.bind, Option.mapM_none, pure, Except.pure,
    List.mapM_nil] at hcore
  simp only [guardedFunctionsMapM_eq
    (applySlotAliasRanges model.fields model.slotAliasRanges)
    model.events model.errors model.adtTypes [] _ hlockfree] at hcore
  rcases hmap :
      ((model.functions.filter
          (fun fn => !fn.isInternal && !isInteropEntrypointName fn.name)).zip selectors).mapM
        (fun x => compileFunctionSpec (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes x.2 x.1) with _ | irFns
  · simp [hmap] at hcore
  · rcases hctor :
        compileConstructor (applySlotAliasRanges model.fields model.slotAliasRanges)
          model.events model.errors model.adtTypes model.constructor with _ | deployStmts
    · simp [hmap, hctor, hnoTemplateEmpty] at hcore
    · refine ⟨irFns, deployStmts, hmap, rfl, ?_⟩
      simp [hmap, hctor, hnoTemplateEmpty] at hcore
      rw [← hcore]
      simp [coreHelperInternalFunctions]

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
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.noFallback hSupported.noReceive
    hSupported.noInternalFunctions (supportedSpec_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hSupported.normalizedFields, hSupported.noAdtTypes] at hmap
  have hcompiled := compiled_functions_forall₂_of_mapM_ok
    model.fields model.events model.errors _ _ hmap
  simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
    hir] using hcompiled

private theorem compileValidatedCore_ok_yields_internalFunctions_nil
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.internalFunctions = [] := by
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.noFallback hSupported.noReceive
    hSupported.noInternalFunctions (supportedSpec_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hir]
  exact coreHelperInternalFunctions_eq_nil model
    hSupported.contractUsesArrayElement_eq_false
    hSupported.contractUsesStorageArrayElement_eq_false
    hSupported.contractUsesDynamicBytesEq_eq_false
    hSupported.contractUsesMulDiv512_eq_false
    hSupported.contractUsesParamDynamicHeadWord_eq_false
    hSupported.noCheckedArithmetic

private theorem compileValidatedCore_ok_yields_deploy_compileConstructor
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    compileConstructor model.fields model.events model.errors [] model.constructor =
      Except.ok ir.deploy := by
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.noFallback hSupported.noReceive
    hSupported.noInternalFunctions (supportedSpec_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hSupported.normalizedFields, hSupported.noAdtTypes] at hctor
  rw [hir]
  exact hctor

private theorem compileValidatedCore_ok_yields_noFallbackEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.fallbackEntrypoint = none := by
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.noFallback hSupported.noReceive
    hSupported.noInternalFunctions (supportedSpec_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hir]

private theorem compileValidatedCore_ok_yields_noReceiveEntrypoint
    (model : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec model selectors)
    (ir : IRContract)
    (hcore : compileValidatedCore model selectors = Except.ok ir) :
    ir.receiveEntrypoint = none := by
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.noFallback hSupported.noReceive
    hSupported.noInternalFunctions (supportedSpec_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hir]

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
  obtain ⟨irFns, deployStmts, hmap, hctor, hir⟩ := compileValidatedCore_ok_inv
    model selectors ir hSupported.surface.noFallback hSupported.surface.noReceive
    hSupported.noInternalFunctions
    (supportedSpecWithScalarEvents_entries_lock_free hSupported)
    hSupported.surface.noTemplateIntrinsics hcore
  rw [hSupported.normalizedFields, hSupported.noAdtTypes] at hmap
  have hcompiled := compiled_functions_forall₂_of_mapM_ok
    model.fields model.events model.errors _ _ hmap
  simpa [SourceSemantics.selectorFunctionPairs, selectorDispatchedFunctions,
    hir] using hcompiled

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
