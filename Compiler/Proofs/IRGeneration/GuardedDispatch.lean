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
