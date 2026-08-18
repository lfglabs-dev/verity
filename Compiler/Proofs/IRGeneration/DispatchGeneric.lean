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
  short `simp` for `interpretIRWithInternals`).

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

private theorem decodeSupportedParamWord_some_of_supported
    (ty : ParamType) (word : Nat) (hsupported : SupportedExternalScalarParamType ty) :
    ∃ value, SourceSemantics.decodeSupportedParamWord ty word = some value := by
  cases ty <;> simp [SupportedExternalScalarParamType, SourceSemantics.decodeSupportedParamWord] at hsupported ⊢

theorem bindSupportedParams_some_of_supported
    (params : List Param) (args : List Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hlen : params.length ≤ args.length) :
    ∃ bindings, SourceSemantics.bindSupportedParams params args = some bindings := by
  induction params generalizing args with
  | nil =>
      exact ⟨[], by simp [SourceSemantics.bindSupportedParams]⟩
  | cons param rest ih =>
      cases args with
      | nil =>
          cases hlen
      | cons arg restArgs =>
          have hparam : SupportedExternalScalarParamType param.ty := hsupported param (by simp)
          rcases decodeSupportedParamWord_some_of_supported param.ty arg hparam with ⟨value, hdecode⟩
          have hrestSupported : ∀ next ∈ rest, SupportedExternalScalarParamType next.ty := by
            intro next hnext
            exact hsupported next (by simp [hnext])
          have hrestLen : rest.length ≤ restArgs.length := Nat.le_of_succ_le_succ hlen
          rcases ih restArgs hrestSupported hrestLen with ⟨bindings, hbindings⟩
          refine ⟨(param.name, value) :: bindings, ?_⟩
          simp [SourceSemantics.bindSupportedParams, hdecode, hbindings]

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

/-- Under supported parameter types, binding only fails on arity. -/
theorem not_length_le_of_bindSupportedParams_none
    (params : List Param) (args : List Nat)
    (hsupported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams params args = none) :
    ¬ params.length ≤ args.length := by
  intro hle
  rcases bindSupportedParams_some_of_supported params args hsupported hle with ⟨b, hb⟩
  rw [hb] at hbindNone
  cases hbindNone

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
    (hsupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    SourceSemantics.interpretFunction model fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  have hlen := Dispatch.not_length_le_of_bindSupportedParams_none
    fn.params tx.args hsupported hbindNone
  have hext := SourceSemantics.bindExternalParams_eq_none_of_not_length_le
    (selector := tx.functionSelector) (params := fn.params) (args := tx.args) hlen
  unfold SourceSemantics.interpretFunction
  rw [hext]

/-- `interpretFunction` reverts whenever external ABI binding fails.  Unlike
`interpretFunction_eq_reverted_of_bind_none` this needs no supportedness
hypothesis: `interpretFunction` matches on `bindExternalParams` directly. -/
theorem interpretFunction_eq_reverted_of_bindExternal_none
    (model : CompilationModel) (fn : FunctionSpec) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hbindNone :
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none) :
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
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none) :
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
    (hsupported : ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
    (hbindNone : SourceSemantics.bindSupportedParams fn.params tx.args = none) :
    SourceSemantics.interpretFunctionWithHelpers model fuel fn tx initialWorld =
      SourceSemantics.revertedResult model
        (SourceSemantics.withTransactionContext initialWorld tx) := by
  have hlen := Dispatch.not_length_le_of_bindSupportedParams_none
    fn.params tx.args hsupported hbindNone
  have hext := SourceSemantics.bindExternalParams_eq_none_of_not_length_le
    (selector := tx.functionSelector) (params := fn.params) (args := tx.args) hlen
  unfold SourceSemantics.interpretFunctionWithHelpers
  rw [hext]

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

section Generic

variable (P : FunctionSpec → Nat → IRFunction → Prop)

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
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (runFn : IRFunction → IRResult)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (irResult : IRResult)
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
    (hinterp : irResult =
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
            runFn irFn
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
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events })
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
          some bindings →
        FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld)
      irResult := by
  have hsel : ∀ fn sel irFn, P fn sel irFn → irFn.selector = sel :=
    fun fn sel irFn hP => (hmeta fn sel irFn hP).2.1
  let pairs := SourceSemantics.selectorFunctionPairs model selectors
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
        · rcases hbindTotal fn hfnMem hlen with ⟨bindings, hbindings⟩
          have hmatch := hfunction fn sel irFn bindings hfnMem hPfn hbindings
          have hlenIr : irFn.params.length ≤ tx.args.length := by
            simpa [hlenEq] using hlen
          rw [hinterp, hfindIr]
          simpa [hfindPairs, hguardFalse, hguardIrFalse, hlenIr] using hmatch
        · have hbindNone :
              SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none :=
            SourceSemantics.bindExternalParams_eq_none_of_not_length_le _ hlen
          have hlenIr : ¬ irFn.params.length ≤ tx.args.length := by
            simpa [hlenEq] using hlen
          rw [hinterp, hfindIr]
          simp [hfindPairs, hguardFalse, hguardIrFalse, hlenIr,
            hSbindFail fn hfnMem hbindNone,
            FunctionBody.sourceResultMatchesIRResult,
            SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
            FunctionBody.encodeStorage_withTransactionContext,
            FunctionBody.encodeEvents_withTransactionContext]

/-- The scalar dispatcher correctness skeleton, now a corollary of the widened
external one: for scalar parameters the external binder agrees with
`bindSupportedParams`, so the syntactic supportedness predicate discharges
`hbindTotal`. -/
theorem interpretContractWith_correct_generic
    (S : FunctionSpec → SourceSemantics.SourceContractResult)
    (runFn : IRFunction → IRResult)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (irResult : IRResult)
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
    (hinterp : irResult =
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
            runFn irFn
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
            events := (FunctionBody.initialIRStateForTx model tx initialWorld).events })
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult (S fn) (runFn irFn)) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWith S model selectors tx initialWorld)
      irResult := by
  refine interpretContractWith_correct_generic_external P S runFn model selectors irFns tx
    initialWorld irResult hmeta ?_ hcompiled ?_ hinterp ?_
  · intro fn hfnMem hbindNone
    refine hSbindFail fn hfnMem ?_
    cases hbind : SourceSemantics.bindSupportedParams fn.params tx.args with
    | none => rfl
    | some bindings =>
        rw [SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams
          tx.functionSelector hbind] at hbindNone
        cases hbindNone
  · intro fn hfnMem hlen
    rcases bindSupportedParams_some_of_supported fn.params tx.args
      (hparamsSupported fn hfnMem) hlen with ⟨bindings, hbindings⟩
    exact ⟨bindings, SourceSemantics.bindExternalParams_eq_some_of_bindSupportedParams
      tx.functionSelector hbindings⟩
  · intro fn sel irFn bindings hfnMem hPfn hbindExt
    rcases bindSupportedParams_some_of_supported fn.params tx.args
      (hparamsSupported fn hfnMem)
      (Dispatch.bindExternalParams_some_length hbindExt) with
      ⟨scalarBindings, hscalar⟩
    exact hfunction fn sel irFn scalarBindings hfnMem hPfn hscalar

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
    hmeta hSbindFail hcompiled hparamsSupported rfl hfunction

/-- Dispatcher correctness, generic over the per-entry compile predicate. -/
theorem interpretContract_correct_of_functions_generic
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalScalarParamType param.ty)
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
      model fn tx initialWorld (hparamsSupported fn hmem) hbindNone)
    hcompiled hparamsSupported hfunction

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
    (fun fn _ hbindNone => interpretFunction_eq_reverted_of_bindExternal_none
      model fn tx initialWorld hbindNone)
    hcompiled hbindTotal hfunction

end Generic

end Compiler.Proofs.IRGeneration
