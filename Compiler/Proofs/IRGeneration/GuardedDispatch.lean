import Compiler.Proofs.IRGeneration.GuardedContractShape
import Compiler.Proofs.IRGeneration.Dispatch

/-!
# Predicate-generic dispatcher correctness and its guarded instance

`interpretContract_correct_of_compiled_functions` fixes the per-entry
characterization to `compileFunctionSpec`.  Its proof only consumes that
predicate through metadata (selector/params/payable) and the per-function
callback — so this module states the dispatcher lemma once, generic over the
compile predicate, and instantiates it for the guarded pipeline with the
metadata facts from `GuardedContractShape`.  The existing theorem statements
are untouched.
-/
namespace Compiler.Proofs.IRGeneration

open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration.Dispatch

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
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
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
  unfold SourceSemantics.interpretContract SourceSemantics.findFunctionBySelector
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
          have hbindExternalNone :
              SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args = none :=
            SourceSemantics.bindExternalParams_eq_none_of_not_length_le tx.functionSelector hlen
          rw [hinterp, hfindIr]
          simp [SourceSemantics.interpretFunction, hbindNone, hbindExternalNone,
            hfindPairs, hguardFalse, hguardIrFalse, hlenIr,
            FunctionBody.sourceResultMatchesIRResult,
            SourceSemantics.revertedResult, FunctionBody.initialIRStateForTx,
            FunctionBody.encodeStorage_withTransactionContext,
            FunctionBody.encodeEvents_withTransactionContext]

end Generic

/-- Guarded instance: dispatcher correctness with entries characterized by
the guarded pipeline. -/
theorem interpretContract_correct_of_compiled_guarded_functions
    (model : CompilationModel) (selectors : List Nat)
    (internalFunctions : List FunctionSpec)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hcompiled : List.Forall₂
      (fun (entry : FunctionSpec × Nat) irFn =>
        compileGuardedFunctionSpec model.fields model.events model.errors []
          internalFunctions entry.2 entry.1 = Except.ok irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hparamsSupported :
      ∀ fn ∈ selectorDispatchedFunctions model,
        ∀ param ∈ fn.params, SupportedExternalParamType param.ty)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        compileGuardedFunctionSpec model.fields model.events model.errors []
          internalFunctions sel fn = Except.ok irFn →
        SourceSemantics.bindSupportedParams fn.params tx.args = some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  interpretContract_correct_of_functions_generic
    (fun fn sel irFn =>
      compileGuardedFunctionSpec model.fields model.events model.errors []
        internalFunctions sel fn = Except.ok irFn)
    model selectors irFns tx initialWorld
    (fun fn sel irFn hP => by
      obtain ⟨hp, hs, hpay⟩ := compileGuardedFunctionSpec_ok_metadata
        model.fields model.events model.errors internalFunctions sel fn irFn hP
      exact ⟨hp, hs, hpay⟩)
    hcompiled hparamsSupported hfunction

end Compiler.Proofs.IRGeneration
