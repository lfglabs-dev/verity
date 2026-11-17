import Compiler.Proofs.IRGeneration.Function
import Compiler.Proofs.IRGeneration.ParamLoading

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# The generic dispatcher correctness skeleton

Every dispatcher theorem in the stack (plain, `WithInternals`, `WithHelpers`,
guarded) shares one proof skeleton: align the source-side selector lookup with
the IR-side `find?`, then case on the payable guard, argument arity, and
parameter binding.  This module states that skeleton once, generic over

- the per-entry compile predicate `P` (consumed only through metadata),
- the per-function source semantics `S` (consumed only through its
  binding-failure behavior), and
- the IR-side executor `runFn` together with an `hinterp` equation pinning the
  interpreter's dispatch shape (discharged by `rfl` for `interpretIR` and by a
  short `simp` for `interpretIRWithInternals`) and its behavior when binding
  fails on arguments that cover every parameter (a dirty scalar word: the
  generated loads revert, see `ParamLoading.exec_genParamLoads_supported_revert`).

All concrete dispatcher theorems derive from `interpretContractWith_correct_generic`.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace Dispatch

def runtimeContractOfFunctions (name : String) (functions : List IRFunction) : IRContract :=
  { name := name
    deploy := []
    constructorPayable := false
    functions := functions
    fallbackEntrypoint := none
    receiveEntrypoint := none
    usesMapping := false
    internalFunctions := [] }

@[simp] theorem runtimeContractOfFunctions_internalFunctions
    (name : String) (functions : List IRFunction) :
    (runtimeContractOfFunctions name functions).internalFunctions = [] := rfl

/-- External binding is arity-faithful: it only succeeds when the ABI head has
at least one word per declared parameter. -/
theorem bindExternalParams_some_length
    {selector : Nat} {params : List Param} {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : SourceSemantics.bindExternalParams selector params args = some bindings) :
    params.length ≤ args.length := by
  by_contra hlen
  rw [SourceSemantics.bindExternalParams_eq_none_of_not_length_le selector hlen] at hbind
  cases hbind

end Dispatch

open Dispatch

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

/-- `interpretFunction` reverts on binding failure (under supported params). -/
theorem interpretFunction_eq_reverted_of_bind_none
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hsupported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams fn.bindingParams tx.args = none) :
    SourceSemantics.interpretFunction model fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  unfold SourceSemantics.interpretFunction
  rw [SourceSemantics.bindExternalParams_eq_none_of_bindSupportedParams_none _ hsupported
    hbindNone]

/-- `interpretFunction` reverts whenever external ABI binding fails.  Unlike
`interpretFunction_eq_reverted_of_bind_none` this needs no supportedness
hypothesis: `interpretFunction` matches on `bindExternalParams` directly. -/
theorem interpretFunction_eq_reverted_of_bindExternal_none
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hbindNone :
      SourceSemantics.bindExternalParams tx.functionSelector fn.bindingParams tx.args = none) :
    SourceSemantics.interpretFunction model fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  unfold SourceSemantics.interpretFunction
  rw [hbindNone]

/-- `interpretFunctionWithHelpers` reverts whenever external ABI binding
fails. -/
theorem interpretFunctionWithHelpers_eq_reverted_of_bindExternal_none
    (model : CompilationModel) (fuel : Nat) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hbindNone :
      SourceSemantics.bindExternalParams tx.functionSelector fn.bindingParams tx.args = none) :
    SourceSemantics.interpretFunctionWithHelpers model fuel fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  unfold SourceSemantics.interpretFunctionWithHelpers
  rw [hbindNone]

/-- `interpretFunctionWithHelpers` reverts on binding failure (under
supported params). -/
theorem interpretFunctionWithHelpers_eq_reverted_of_bind_none
    (model : CompilationModel) (fuel : Nat) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hsupported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams fn.bindingParams tx.args = none) :
    SourceSemantics.interpretFunctionWithHelpers model fuel fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  unfold SourceSemantics.interpretFunctionWithHelpers
  rw [SourceSemantics.bindExternalParams_eq_none_of_bindSupportedParams_none _ hsupported
    hbindNone]

/-- `interpretContract` is the `interpretContractWith` instance at
`interpretFunction`. -/
theorem interpretContract_eq_interpretContractWith
    (model : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.interpretContract model selectors tx initialWorld =
      interpretContractWith
        (fun fn => SourceSemantics.interpretFunction model fn tx initialWorld)
        model selectors tx initialWorld := by
  unfold SourceSemantics.interpretContract interpretContractWith
  cases SourceSemantics.findFunctionBySelector model selectors tx.functionSelector <;> rfl

/-- `interpretContractWithHelpers` is the `interpretContractWith` instance at
`interpretFunctionWithHelpers`. -/
theorem interpretContractWithHelpers_eq_interpretContractWith
    (model : CompilationModel) (selectors : List Nat) (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.interpretContractWithHelpers model selectors fuel tx initialWorld =
      interpretContractWith
        (fun fn => SourceSemantics.interpretFunctionWithHelpers model fuel fn tx initialWorld)
        model selectors tx initialWorld := by
  unfold SourceSemantics.interpretContractWithHelpers interpretContractWith
  cases SourceSemantics.findFunctionBySelector model selectors tx.functionSelector <;> rfl

/-- The IR dispatcher's rollback record, returned when the selector lookup,
the payable guard, or the argument-arity check fails. -/
private abbrev revertedIRResult (model : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) : IRResult :=
  { success := false
    returnValue := none
    finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
    finalMappings := Compiler.Proofs.storageAsMappings
      (FunctionBody.initialIRStateForTx model tx initialWorld).storage
    events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }

/-- The IR dispatcher's result once the selector lookup has found `irFn`: the
payable guard, then the argument-arity check, around the executor `runFn`. -/
private abbrev selectedIRResult (model : CompilationModel) (runFn : IRFunction → IRResult)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (irFn : IRFunction) : IRResult :=
  if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
    revertedIRResult model tx initialWorld
  else if irFn.params.length ≤ tx.args.length then runFn irFn
  else revertedIRResult model tx initialWorld

private theorem reverted_matches_revertedIRResult
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
      (revertedIRResult model tx initialWorld) := by
  simp [FunctionBody.sourceResultMatchesIRResult,
    SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
    FunctionBody.encodeStorage_withTransactionContext,
    FunctionBody.encodeEvents_withTransactionContext]

/-- Past the payable guard, the selected function's arity check agrees on both
sides, and so does a binding failure on arguments that pass it (`hIRbindFail`:
the IR executor reverts too). -/
private theorem dispatch_selected_arity_matches
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (runFn : IRFunction → IRResult) (model : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (fn : FunctionSpec) (irFn : IRFunction)
    (hlenEq : irFn.params.length = fn.params.length)
    (hIRbindFail : fn.params.length ≤ tx.args.length →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none →
      FunctionBody.sourceResultMatchesIRResult
        (SourceSemantics.revertedResult model
          (SourceSemantics.withTransactionContext initialWorld tx)) (runFn irFn))
    (hSbindFail :
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hfunction : ∀ bindings,
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    FunctionBody.sourceResultMatchesIRResult (S fn)
      (if irFn.params.length ≤ tx.args.length then runFn irFn
        else revertedIRResult model tx initialWorld) := by
  rw [hlenEq]
  by_cases hlen : fn.params.length ≤ tx.args.length
  · rw [if_pos hlen]
    cases hbindings : SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args with
    | some bindings => exact hfunction bindings hbindings
    | none => rw [hSbindFail hbindings]; exact hIRbindFail hlen hbindings
  · rw [if_neg hlen,
      hSbindFail (SourceSemantics.bindExternalParams_eq_none_of_not_length_le _ hlen)]
    exact reverted_matches_revertedIRResult model tx initialWorld

/-- Past the selector lookup, the payable guard agrees on both sides. -/
private theorem dispatch_selected_matches
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (runFn : IRFunction → IRResult) (model : CompilationModel) (tx : IRTransaction)
    (initialWorld : Verity.ContractState) (fn : FunctionSpec) (irFn : IRFunction)
    (hpayableEq : irFn.payable = fn.isPayable)
    (harity : FunctionBody.sourceResultMatchesIRResult (S fn)
      (if irFn.params.length ≤ tx.args.length then runFn irFn
        else revertedIRResult model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (if !fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        SourceSemantics.revertedResult model
          (SourceSemantics.withTransactionContext initialWorld tx)
      else S fn)
      (if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        revertedIRResult model tx initialWorld
      else if irFn.params.length ≤ tx.args.length then runFn irFn
      else revertedIRResult model tx initialWorld) := by
  rw [hpayableEq]
  by_cases hguard : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = true
  · rw [if_pos hguard, if_pos hguard]
    exact reverted_matches_revertedIRResult model tx initialWorld
  · rw [if_neg hguard, if_neg hguard]
    exact harity

private theorem mem_selectorDispatchedFunctions_of_find_pair
    {model : CompilationModel} {selectors : List Nat} {selector : Nat}
    {fn : FunctionSpec} {sel : Nat}
    (hfind : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == selector) = some (fn, sel)) :
    fn ∈ selectorDispatchedFunctions model := by
  have hpairMem := List.mem_of_find?_eq_some hfind
  simpa [SourceSemantics.selectorFunctionPairs] using (List.of_mem_zip hpairMem).1

/-- Source dispatch on a selector lookup hit. -/
private theorem interpretContractWith_of_find_pair
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    {model : CompilationModel} {selectors : List Nat} {tx : IRTransaction}
    (initialWorld : Verity.ContractState) {fn : FunctionSpec} {sel : Nat}
    (hfind : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == tx.functionSelector) = some (fn, sel)) :
    interpretContractWith S model selectors tx initialWorld =
      if !fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        SourceSemantics.revertedResult model
          (SourceSemantics.withTransactionContext initialWorld tx)
      else S fn := by
  unfold interpretContractWith SourceSemantics.findFunctionBySelector
  rw [hfind]
  rfl

/-- Source dispatch on a selector lookup miss. -/
private theorem interpretContractWith_of_find_none
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    {model : CompilationModel} {selectors : List Nat} {tx : IRTransaction}
    (initialWorld : Verity.ContractState)
    (hfind : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == tx.functionSelector) = none) :
    interpretContractWith S model selectors tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  unfold interpretContractWith SourceSemantics.findFunctionBySelector
  rw [hfind]
  rfl

/-- Selector-hit branch of the skeleton, once the IR result is pinned to the
selected function's guarded execution and its arity branch is matched. -/
private theorem dispatch_find_pair_matches
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (runFn : IRFunction → IRResult) {model : CompilationModel} {selectors : List Nat}
    {tx : IRTransaction} (initialWorld : Verity.ContractState) {irResult : IRResult}
    {fn : FunctionSpec} {sel : Nat} {irFn : IRFunction}
    (hfindPairs : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == tx.functionSelector) = some (fn, sel))
    (hirResult : irResult = selectedIRResult model runFn tx initialWorld irFn)
    (hpayableEq : irFn.payable = fn.isPayable)
    (harity : FunctionBody.sourceResultMatchesIRResult (S fn)
      (if irFn.params.length ≤ tx.args.length then runFn irFn
        else revertedIRResult model tx initialWorld)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld) irResult := by
  rw [interpretContractWith_of_find_pair S initialWorld hfindPairs, hirResult]
  exact dispatch_selected_matches S runFn model tx initialWorld fn irFn hpayableEq harity

/-- Selector-miss branch of the skeleton. -/
private theorem dispatch_find_none_matches
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    {model : CompilationModel} {selectors : List Nat} {tx : IRTransaction}
    (initialWorld : Verity.ContractState) {irResult : IRResult}
    (hfindPairs : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == tx.functionSelector) = none)
    (hirResult : irResult = revertedIRResult model tx initialWorld) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld) irResult := by
  rw [interpretContractWith_of_find_none S initialWorld hfindPairs, hirResult]
  exact reverted_matches_revertedIRResult model tx initialWorld

section Generic

variable (P : FunctionSpec → Nat → IRFunction → Prop)

/-- The IR executor reverts like the source whenever scalar binding rejects
arguments that pass the arity check (a dirty scalar head word: the generated
loads revert, `ParamLoading.exec_genParamLoads_supported_revert`). -/
abbrev ScalarBindFailReverts (runFn : IRFunction → IRResult) (model : CompilationModel)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) : Prop :=
  ∀ fn sel irFn, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
    fn.params.length ≤ tx.args.length →
    SourceSemantics.bindSupportedParams fn.params tx.args = none →
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx)) (runFn irFn)

/-- Selector alignment of `find?` under any selector-faithful predicate. -/
theorem find_function_some_of_forall₂_generic
    (hsel : ∀ fn sel irFn, P fn sel irFn → irFn.selector = sel)
    (selector : Nat)
    {pairs : List (FunctionSpec × Nat)} {irFns : List IRFunction}
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      pairs irFns)
    {fn : FunctionSpec} {sel : Nat}
    (hfind : pairs.find? (fun entry => entry.2 == selector) = some (fn, sel)) :
    ∃ irFn,
      irFns.find? (fun irFn => irFn.selector == selector) = some irFn ∧
      P fn sel irFn := by
  induction hcompiled generalizing fn sel with
  | nil => simp at hfind
  | @cons entry irFn pairs irFns hhead hrest ih =>
      rcases entry with ⟨headFn, headSel⟩
      by_cases hselEq : headSel = selector
      · simp [hselEq] at hfind
        rcases hfind with ⟨rfl, rfl⟩
        refine ⟨irFn, ?_, by simpa [hselEq] using hhead⟩
        have hselector : irFn.selector = selector := by
          calc irFn.selector = headSel := hsel headFn headSel irFn hhead
            _ = selector := hselEq
        simp [hselector]
      · have hfindRest :
            pairs.find? (fun entry => entry.2 == selector) = some (fn, sel) := by
          simpa [hselEq] using hfind
        rcases ih hfindRest with ⟨irFn', hfindIr, hP⟩
        refine ⟨irFn', ?_, hP⟩
        have hheadSelector : irFn.selector = headSel :=
          hsel headFn headSel irFn hhead
        simp [hselEq, hheadSelector, hfindIr]

theorem find_function_none_of_forall₂_generic
    (hsel : ∀ fn sel irFn, P fn sel irFn → irFn.selector = sel)
    (selector : Nat)
    {pairs : List (FunctionSpec × Nat)} {irFns : List IRFunction}
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      pairs irFns)
    (hfind : pairs.find? (fun entry => entry.2 == selector) = none) :
    irFns.find? (fun irFn => irFn.selector == selector) = none := by
  induction hcompiled with
  | nil => simp
  | @cons entry irFn pairs irFns hhead hrest ih =>
      rcases entry with ⟨headFn, headSel⟩
      by_cases hselEq : headSel = selector
      · simp [hselEq] at hfind
      · have hfindRest :
            pairs.find? (fun entry => entry.2 == selector) = none := by
          simpa [hselEq] using hfind
        have hheadSelector : irFn.selector = headSel :=
          hsel headFn headSel irFn hhead
        simp [hselEq, hheadSelector, ih hfindRest]

private theorem selector_eq_of_meta
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable) :
    ∀ fn sel irFn, P fn sel irFn → irFn.selector = sel :=
  fun fn sel irFn hP => (hmeta fn sel irFn hP).2.1

/-- The skeleton against a pointwise description of the IR dispatch result
(`hnone`/`hsome`), given that every selected function's arity branch matches. -/
private theorem interpretContractWith_matches_of_lookup
    (S : FunctionSpec → SourceSemantics.SourceContractResult) (runFn : IRFunction → IRResult)
    (model : CompilationModel) (selectors : List Nat) (irFns : List IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (irResult : IRResult)
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hhit : ∀ fn sel irFn, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
      FunctionBody.sourceResultMatchesIRResult (S fn)
        (if irFn.params.length ≤ tx.args.length then runFn irFn
          else revertedIRResult model tx initialWorld))
    (hnone : irFns.find? (fun irFn => irFn.selector == tx.functionSelector) = none →
      irResult = revertedIRResult model tx initialWorld)
    (hsome : ∀ irFn, irFns.find? (fun irFn => irFn.selector == tx.functionSelector) = some irFn →
      irResult = selectedIRResult model runFn tx initialWorld irFn) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld) irResult := by
  have hsel := selector_eq_of_meta P hmeta
  rcases hfindPairs : (SourceSemantics.selectorFunctionPairs model selectors).find?
      (fun entry => entry.2 == tx.functionSelector) with _ | ⟨fn, sel⟩
  · exact dispatch_find_none_matches S initialWorld hfindPairs
      (hnone (find_function_none_of_forall₂_generic P hsel _ hcompiled hfindPairs))
  obtain ⟨irFn, hfindIr, hPfn⟩ :=
    find_function_some_of_forall₂_generic P hsel _ hcompiled hfindPairs
  exact dispatch_find_pair_matches S runFn initialWorld hfindPairs (hsome irFn hfindIr)
    (hmeta fn sel irFn hPfn).2.2
    (hhit fn sel irFn (mem_selectorDispatchedFunctions_of_find_pair hfindPairs) hPfn)

private theorem dispatch_hit_of_external
    (S : FunctionSpec → SourceSemantics.SourceContractResult) (runFn : IRFunction → IRResult)
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hbindTotal : ∀ fn ∈ selectorDispatchedFunctions model, fn.params.length ≤ tx.args.length →
      ∃ bindings, SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
        some bindings)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    ∀ fn sel irFn, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
    FunctionBody.sourceResultMatchesIRResult (S fn)
      (if irFn.params.length ≤ tx.args.length then runFn irFn
        else revertedIRResult model tx initialWorld) := fun fn sel irFn hfnMem hPfn =>
  dispatch_selected_arity_matches S runFn model tx initialWorld fn irFn
    (by simp [(hmeta fn sel irFn hPfn).1])
    (fun hlen hnone => absurd hnone (by
      obtain ⟨bindings, hbindings⟩ := hbindTotal fn hfnMem hlen
      simp [hbindings]))
    (hSbindFail fn hfnMem) (hfunction fn sel irFn · hfnMem hPfn)

private theorem bindSupportedParams_some_of_bindExternalParams_some
    {selector : Nat} {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hbindExt : SourceSemantics.bindExternalParams selector params args = some bindings) :
    ∃ scalarBindings, SourceSemantics.bindSupportedParams params args = some scalarBindings := by
  cases hbind : SourceSemantics.bindSupportedParams params args with
  | some scalarBindings => exact ⟨scalarBindings, rfl⟩
  | none =>
      rw [SourceSemantics.bindExternalParams_eq_none_of_bindSupportedParams_none selector
        hsupported hbind] at hbindExt
      cases hbindExt

private theorem bindSupportedParams_none_of_bindExternalParams_none
    {selector : Nat} {params : List Param} {args : List Nat}
    (hbindNone : SourceSemantics.bindExternalParams selector params args = none) :
    SourceSemantics.bindSupportedParams params args = none := by
  cases hbind : SourceSemantics.bindSupportedParams params args with
  | none => rfl
  | some bindings =>
      rw [SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams
        selector hbind] at hbindNone
      cases hbindNone

/-- The master dispatcher correctness skeleton, phrased over the *external*
ABI binder `bindExternalParams`.  This is the widened form: it covers every
parameter shape the external binder understands (scalars and the
length-prefixed dynamic ones such as `bytes`), because supportedness enters
only through `hbindTotal` — "arity suffices for binding to succeed" — rather
than through a syntactic predicate on `ParamType`.

Generic over the compile predicate `P`, the per-function source semantics `S`,
and the IR-side executor `runFn`.  The `hinterp` equation pins the
interpreter's dispatch shape. -/
theorem interpretContractWith_correct_generic_external
    (S : FunctionSpec → SourceSemantics.SourceContractResult) (runFn : IRFunction → IRResult)
    (model : CompilationModel) (selectors : List Nat) (irFns : List IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (irResult : IRResult)
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hbindTotal : ∀ fn ∈ selectorDispatchedFunctions model, fn.params.length ≤ tx.args.length →
      ∃ bindings, SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
        some bindings)
    (hinterp : irResult =
      match irFns.find? (fun irFn => irFn.selector == tx.functionSelector) with
      | some irFn =>
          if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
            { success := false, returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
          else if irFn.params.length ≤ tx.args.length then runFn irFn else
            { success := false, returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
      | none =>
          { success := false, returnValue := none
            finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            finalMappings := Compiler.Proofs.storageAsMappings
              (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events })
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld) irResult := by
  exact interpretContractWith_matches_of_lookup P S runFn model selectors irFns tx initialWorld
    irResult hmeta hcompiled (dispatch_hit_of_external P S runFn model tx initialWorld hmeta
      hSbindFail hbindTotal hfunction) (by rw [hinterp, ·]) (fun _ h => by rw [hinterp, h])

private theorem dispatch_hit_of_scalar
    (S : FunctionSpec → SourceSemantics.SourceContractResult) (runFn : IRFunction → IRResult)
    (model : CompilationModel) (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindSupportedParams fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hIRbindFail : ScalarBindFailReverts P runFn model tx initialWorld)
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    ∀ fn sel irFn, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
    FunctionBody.sourceResultMatchesIRResult (S fn)
      (if irFn.params.length ≤ tx.args.length then runFn irFn
        else revertedIRResult model tx initialWorld) := fun fn sel irFn hfn hP =>
  dispatch_selected_arity_matches S runFn model tx initialWorld fn irFn
    (by simp [(hmeta fn sel irFn hP).1])
    (fun hlen h => hIRbindFail fn sel irFn hfn hP hlen
      (bindSupportedParams_none_of_bindExternalParams_none h))
    (fun h => hSbindFail fn hfn (bindSupportedParams_none_of_bindExternalParams_none h))
    (fun _ hbind =>
      (bindSupportedParams_some_of_bindExternalParams_some (hparamsSupported fn hfn) hbind).elim
        fun scalarBindings hscalar => hfunction fn sel irFn scalarBindings hfn hP hscalar)

/-- The scalar dispatcher correctness skeleton.  For scalar parameters the
external binder agrees with `bindSupportedParams`; a binding failure on
arguments that pass the arity check (a dirty scalar word) reverts the source,
and `hIRbindFail` states the IR executor reverts too. -/
theorem interpretContractWith_correct_generic
    (S : FunctionSpec → SourceSemantics.SourceContractResult) (runFn : IRFunction → IRResult)
    (model : CompilationModel) (selectors : List Nat) (irFns : List IRFunction)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) (irResult : IRResult)
    (hmeta : ∀ fn sel irFn, P fn sel irFn → irFn.params = fn.params.map Param.toIRParam ∧
      irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindSupportedParams fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported : ∀ fn ∈ selectorDispatchedFunctions model,
      ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hIRbindFail : ScalarBindFailReverts P runFn model tx initialWorld)
    (hinterp : irResult =
      match irFns.find? (fun irFn => irFn.selector == tx.functionSelector) with
      | some irFn =>
          if !irFn.payable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
            { success := false, returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
          else if irFn.params.length ≤ tx.args.length then runFn irFn else
            { success := false, returnValue := none
              finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              finalMappings := Compiler.Proofs.storageAsMappings
                (FunctionBody.initialIRStateForTx model tx initialWorld).storage
              events := (FunctionBody.initialIRStateForTx model tx initialWorld).events }
      | none =>
          { success := false, returnValue := none
            finalStorage := (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            finalMappings := Compiler.Proofs.storageAsMappings
              (FunctionBody.initialIRStateForTx model tx initialWorld).storage
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events })
    (hfunction : ∀ fn sel irFn bindings, fn ∈ selectorDispatchedFunctions model → P fn sel irFn →
      SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
      FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld) irResult := by
  exact interpretContractWith_matches_of_lookup P S runFn model selectors irFns tx initialWorld
    irResult hmeta hcompiled (dispatch_hit_of_scalar P S runFn model tx initialWorld hmeta
      hSbindFail hparamsSupported hIRbindFail hfunction) (by rw [hinterp, ·])
      (fun _ h => by rw [hinterp, h])

/-- Source-parametric dispatcher correctness against `interpretIR`: the
master skeleton with the executor fixed to `execIRFunction` (the `hinterp`
dispatch equation holds by `rfl`). -/
theorem interpretContractWith_correct_of_functions_generic
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
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hIRbindFail : ScalarBindFailReverts P (fun irFn => execIRFunction irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld)) model tx initialWorld)
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
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  interpretContractWith_correct_generic P S
    (fun irFn => execIRFunction irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld))
    model selectors irFns tx initialWorld _
    hmeta hSbindFail hcompiled hparamsSupported hIRbindFail rfl hfunction

/-- Dispatcher correctness, generic over the per-entry compile predicate. -/
theorem interpretContract_correct_of_functions_generic
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    {habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard}
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hIRbindFail : ScalarBindFailReverts P (fun irFn => execIRFunction irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld)) model tx initialWorld)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretContract_eq_interpretContractWith]
  exact interpretContractWith_correct_of_functions_generic P
    (fun fn => SourceSemantics.interpretFunction model fn tx initialWorld)
    model selectors irFns tx initialWorld hmeta
    (fun fn hmem hbindNone => interpretFunction_eq_reverted_of_bind_none
      model fn tx initialWorld
        (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hparamsSupported fn hmem)
        (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hbindNone))
    hcompiled hparamsSupported hIRbindFail hfunction

/-- Widened source-parametric dispatcher correctness against `interpretIR`:
the external skeleton with the executor fixed to `execIRFunction`. -/
theorem interpretContractWith_correct_of_functions_generic_external
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hSbindFail : ∀ fn, fn ∈ selectorDispatchedFunctions model →
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none →
      S fn = SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx))
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hbindTotal :
      ∀ fn ∈ selectorDispatchedFunctions model,
        fn.params.length ≤ tx.args.length →
        ∃ bindings,
          SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
            some bindings)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
          some bindings →
        FunctionBody.sourceResultMatchesIRResult (S fn)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  interpretContractWith_correct_generic_external P S
    (fun irFn => execIRFunction irFn tx.args
      (FunctionBody.initialIRStateForTx model tx initialWorld))
    model selectors irFns tx initialWorld _
    hmeta hSbindFail hcompiled hbindTotal rfl hfunction

/-- Widened dispatcher correctness for `interpretContract`, generic over the
per-entry compile predicate.  Parameter supportedness enters only through
`hbindTotal`, so this covers `bytes` (and every other shape the external ABI
binder decodes) in addition to the scalars.

`hbindTotal` is not free for a dynamic parameter: unlike the scalar case it
does not follow from arity, since a malformed offset or a truncated tail makes
the binder fail.  `Compiler/Proofs/IRGeneration/DispatchBytesParam.lean`
discharges it at `bytes` from the ABI encoder, which is what makes the
instantiation there non-vacuous. -/
theorem interpretContract_correct_of_functions_generic_external
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    {habi : ∀ fn ∈ selectorDispatchedFunctions model, fn.abiDecoding = .standard}
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hbindTotal :
      ∀ fn ∈ selectorDispatchedFunctions model,
        fn.params.length ≤ tx.args.length →
        ∃ bindings,
          SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
            some bindings)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
          some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) := by
  rw [interpretContract_eq_interpretContractWith]
  exact interpretContractWith_correct_of_functions_generic_external P
    (fun fn => SourceSemantics.interpretFunction model fn tx initialWorld)
    model selectors irFns tx initialWorld hmeta
    (fun fn hmem hbindNone => interpretFunction_eq_reverted_of_bindExternal_none
      model fn tx initialWorld
        (by simpa [FunctionSpec.bindingParams, habi fn hmem] using hbindNone))
    hcompiled hbindTotal hfunction

end Generic

end Compiler.Proofs.IRGeneration
