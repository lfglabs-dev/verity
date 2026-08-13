import Compiler.Proofs.IRGeneration.GuardedSourceBridge

/-!
# The guarded whole-contract theorem (`compile_preserves_semantics_guarded`)

Assembles the family: the source-parametric dispatcher (per-entry source
semantics abstracted alongside the compile predicate), the guarded source
contract semantics (`interpretGuardedContract`), and the final additive
whole-contract statement — contracts whose functions may carry
`nonreentrant(lock)` annotations, characterized by the guarded pipeline with
no lock-free erasure.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.Dispatch
open Compiler.Proofs.IRGeneration.Contract
open Verity.Core.NonReentrantGuard

/-- Source contract dispatch with a parametric per-function semantics. -/
def interpretContractWith
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  match SourceSemantics.findFunctionBySelector spec selectors tx.functionSelector with
  | some fn =>
      if !fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        SourceSemantics.revertedResult spec
          (SourceSemantics.withTransactionContext initialWorld tx)
      else S fn
  | none =>
      SourceSemantics.revertedResult spec
        (SourceSemantics.withTransactionContext initialWorld tx)

/-- The per-function guarded choice: annotated functions with a resolved lock
run the guarded semantics; everything else runs the plain semantics. -/
def guardedFunctionChoice (spec : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (fn : FunctionSpec) :
    SourceSemantics.SourceContractResult :=
  match fn.nonReentrantLock with
  | none => SourceSemantics.interpretFunction spec fn tx initialWorld
  | some lockField =>
      match findFieldWithResolvedSlot spec.fields lockField with
      | some (_, slot) => interpretGuardedFunction spec slot fn tx initialWorld
      | none => SourceSemantics.interpretFunction spec fn tx initialWorld

/-- Guarded source contract semantics. -/
def interpretGuardedContract (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  interpretContractWith (guardedFunctionChoice spec tx initialWorld)
    spec selectors tx initialWorld

/-- The reverted result ignores the lock overlay. -/
theorem revertedResult_setLock (spec : CompilationModel)
    (world : Verity.ContractState) (slot : Nat) (v : Verity.Uint256) :
    SourceSemantics.revertedResult spec (setLock slot v world) =
      SourceSemantics.revertedResult spec world := by
  unfold SourceSemantics.revertedResult
  congr 1
  funext s
  exact encodeStorageAt_setLock _ world slot v s

/-- Source-parametric dispatcher correctness: like the predicate-generic
version, additionally abstracting the per-function source semantics.  The
only structural requirement on `S` is that it reverts on binding failure. -/
theorem interpretContractWith_correct_of_functions_generic
    (P : FunctionSpec → Nat → IRFunction → Prop)
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindSupportedParams fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult (S fn)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hsel : ∀ fn sel irFn, P fn sel irFn → irFn.selector = sel :=
    fun fn sel irFn hP => (hmeta fn sel irFn hP).2.1
  let pairs := SourceSemantics.selectorFunctionPairs model selectors
  have hinterp :
      interpretIR (runtimeContractOfFunctions model.name irFns) tx
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
            execIRFunction irFn tx.args (FunctionBody.initialIRStateForTx model tx initialWorld)
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
        rfl
  unfold interpretContractWith SourceSemantics.findFunctionBySelector
  cases hfindPairs :
      pairs.find? (fun entry => entry.2 == tx.functionSelector) with
  | none =>
      have hfindIr :
          irFns.find? (fun irFn => irFn.selector == tx.functionSelector) = none :=
        find_function_none_of_forall₂_generic P hsel tx.functionSelector
          hcompiled hfindPairs
      rw [hinterp, hfindIr]
      simp [hfindPairs, FunctionBody.sourceResultMatchesIRResult,
        SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
        FunctionBody.encodeStorage_withTransactionContext,
        FunctionBody.encodeEvents_withTransactionContext]
  | some pair =>
      rcases pair with ⟨fn, sel⟩
      rcases find_function_some_of_forall₂_generic P hsel tx.functionSelector
          hcompiled hfindPairs with ⟨irFn, hfindIr, hPfn⟩
      have hpairMem : (fn, sel) ∈ pairs := List.mem_of_find?_eq_some hfindPairs
      have hfnMem : fn ∈ selectorDispatchedFunctions model := by
        simpa [pairs, SourceSemantics.selectorFunctionPairs] using
          (List.of_mem_zip hpairMem).1
      obtain ⟨hparamsEq, _, hpayableEq⟩ := hmeta fn sel irFn hPfn
      have hlenEq : irFn.params.length = fn.params.length := by
        simpa [hparamsEq]
      by_cases hguard : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = true
      · have hguardIr :
            (!irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0) = true := by
          simpa [hpayableEq] using hguard
        rw [hinterp, hfindIr]
        simp [hfindPairs, hguard, hguardIr, FunctionBody.sourceResultMatchesIRResult,
          SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
          FunctionBody.encodeStorage_withTransactionContext,
          FunctionBody.encodeEvents_withTransactionContext]
      · have hguardFalse :
            (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false :=
          Bool.eq_false_iff.2 hguard
        have hguardIrFalse :
            (!irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false := by
          simpa [hpayableEq] using hguardFalse
        by_cases hlen : fn.params.length ≤ tx.args.length
        · rcases bindSupportedParams_some_of_supported fn.params tx.args
              (hparamsSupported fn hfnMem) hlen with ⟨bindings, hbindings⟩
          have hmatch := hfunction fn sel irFn bindings hfnMem hPfn hbindings
          have hlenIr : irFn.params.length ≤ tx.args.length := by
            simpa [hlenEq] using hlen
          rw [hinterp, hfindIr]
          simpa [hfindPairs, hguardFalse, hguardIrFalse, hlenIr] using hmatch
        · have hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none := by
            cases hbind : SourceSemantics.bindSupportedParams fn.params tx.args with
            | none => rfl
            | some bindings =>
                exact absurd (ParamLoading.bindSupportedParams_some_length hbind) hlen
          have hlenIr : ¬ irFn.params.length ≤ tx.args.length := by
            simpa [hlenEq] using hlen
          rw [hinterp, hfindIr]
          simp [hfindPairs, hguardFalse, hguardIrFalse, hlenIr,
            hSbindFail fn hfnMem hbindNone,
            FunctionBody.sourceResultMatchesIRResult,
            SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
            FunctionBody.encodeStorage_withTransactionContext,
            FunctionBody.encodeEvents_withTransactionContext]

theorem SupportedFunctionGuarded.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (h : SupportedFunctionGuarded spec fn) :
    ∀ param ∈ fn.params, SupportedExternalParamType param.ty :=
  h.params.supported

theorem supported_params_of_supportedSpecGuarded
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecGuarded model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

/-- The guarded choice reverts on binding failure (under supported params,
binding only fails on arity, where both the plain and the guarded semantics
revert — the lock overlay is invisible in the reverted result). -/
theorem guardedFunctionChoice_bindFail (model : CompilationModel)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (fn : FunctionSpec)
    (hparams : ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    guardedFunctionChoice model tx initialWorld fn =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  have hlen : ¬ fn.params.length ≤ tx.args.length := by
    intro hle
    rcases bindSupportedParams_some_of_supported fn.params tx.args hparams hle
      with ⟨bindings, hb⟩
    rw [hb] at hbindNone
    cases hbindNone
  have hext := SourceSemantics.bindExternalParams_eq_none_of_not_length_le
    (selector := tx.functionSelector) (params := fn.params)
    (args := tx.args) hlen
  have hplain : ∀ world, SourceSemantics.interpretFunction model fn tx world =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext world tx) := by
    intro world
    unfold SourceSemantics.interpretFunction
    rw [hext]
  unfold guardedFunctionChoice
  cases hnl : fn.nonReentrantLock with
  | none =>
      simp only [hnl]
      exact hplain initialWorld
  | some lockField =>
      simp only [hnl]
      cases hfield : findFieldWithResolvedSlot model.fields lockField with
      | none =>
          simp only [hfield]
          exact hplain initialWorld
      | some fs =>
          obtain ⟨field, slot⟩ := fs
          simp only [hfield]
          unfold interpretGuardedFunction
          by_cases hlock : (initialWorld.transientStorage slot).val = 1
          · rw [if_pos hlock]
          · rw [if_neg hlock, hplain (setLock slot 1 initialWorld),
              withTransactionContext_setLock, revertedResult_setLock]

/-- The guarded whole-contract theorem: contracts whose functions may carry
`nonreentrant(lock)` annotations, characterized by the guarded pipeline (no
lock-free erasure), match the guarded source semantics — given the
per-function correspondence supplied by the caller (dischargeable via
`interpretGuardedFunction_matches` from the family root and the base
correspondence at the lock-acquired world). -/
theorem compile_preserves_semantics_guarded
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecGuarded model selectors)
    (ir : IRContract) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompile : CompilationModel.compile model selectors = Except.ok ir)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileGuardedFunctionSpec model.fields model.events model.errors []
          [] sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (guardedFunctionChoice model tx initialWorld fn)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretGuardedContract model selectors tx initialWorld)
      (interpretIR ir tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  have hcompiled := compile_ok_yields_guarded_functions model selectors
    hSupported ir hcompile
  have hparamsSupported := supported_params_of_supportedSpecGuarded
    model selectors hSupported
  rw [interpretIR_eq_runtimeContractOfFunctions
    (ir := ir) (runtimeName := model.name) (irFns := ir.functions)
    (tx := tx)
    (initialState := FunctionBody.initialIRStateForTx model tx initialWorld)
    (hfunctions := rfl)]
  exact interpretContractWith_correct_of_functions_generic
    (fun fn sel irFn =>
      compileGuardedFunctionSpec model.fields model.events model.errors []
        [] sel fn = Except.ok irFn)
    (guardedFunctionChoice model tx initialWorld)
    model selectors ir.functions tx initialWorld
    (fun fn sel irFn hP => compileGuardedFunctionSpec_ok_metadata
      model.fields model.events model.errors [] sel fn irFn hP)
    (fun fn hmem hbindNone => guardedFunctionChoice_bindFail model tx
      initialWorld fn (hparamsSupported fn hmem) hbindNone)
    hcompiled hparamsSupported hfunction

end Compiler.Proofs.IRGeneration
