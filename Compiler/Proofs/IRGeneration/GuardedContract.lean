import Compiler.Proofs.IRGeneration.GuardedSourceBridge

set_option linter.unusedSimpArgs false

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

theorem SupportedFunctionGuarded.paramsSupported
    {spec : CompilationModel} {fn : FunctionSpec}
    (h : SupportedFunctionGuarded spec fn) :
    ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty :=
  h.params.supported

theorem supported_params_of_supportedSpecGuarded
    (model : CompilationModel) (selectors : List Nat)
    (hSupported : SupportedSpecGuarded model selectors) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty := by
  intro fn hfn param hparam
  have hfnModel : fn ∈ model.functions := List.mem_of_mem_filter hfn
  exact (hSupported.functions fn hfnModel).paramsSupported param hparam

/-- The guarded choice reverts on binding failure (under supported params,
binding only fails on arity, where both the plain and the guarded semantics
revert — the lock overlay is invisible in the reverted result). -/
theorem guardedFunctionChoice_bindFail (model : CompilationModel)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (fn : FunctionSpec)
    (hparams : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
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
