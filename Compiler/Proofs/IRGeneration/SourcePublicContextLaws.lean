import Compiler.Proofs.IRGeneration.SourceSemantics

/-! Public Source entry transport with explicit context and receipt schedule.
These laws expose the exact executed body and rollback projection; supplied
context is not an authentication or a whole-function gas certificate. -/
namespace Compiler.Proofs.IRGeneration.SourcePublicContextLaws
open Compiler.CompilationModel SourceSemantics

/-- Actual terminal exception from the supplied body frame, with rollback. -/
theorem function_exception
    (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (terminal : RuntimeState)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (body : execStmtListWithEvents (effectiveFields spec) spec.events
        { world := withTransactionContext initialWorld tx, bindings := bindings,
          selector := tx.functionSelector, externalCallOracle := oracle,
          executionContext := context, externalCallIndex := index, errors := spec.errors } fn.body = .exceptional terminal) :
    interpretFunction spec fn tx initialWorld oracle context index =
      exceptionalResult spec (withTransactionContext initialWorld tx) terminal := by
  simp only [interpretFunction, bound, body]

/-- Actual terminal exception from the supplied body frame, with rollback. -/
theorem constructor_exception
    (spec : CompilationModel) (ctor : ConstructorSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (terminal : RuntimeState)
    (raw : constructorTouchesUnsupportedRawCalldataSurface spec ctor = false)
    (bound : constructorExecutionBindings ctor tx.args = some bindings)
    (body : execStmtListWithEvents (effectiveFields spec) spec.events
        { world := withTransactionContext initialWorld tx, bindings := bindings,
          selector := tx.functionSelector, externalCallOracle := oracle,
          executionContext := context, externalCallIndex := index } ctor.body = .exceptional terminal) :
    interpretConstructor spec ctor tx initialWorld oracle context index =
      exceptionalResult spec (withTransactionContext initialWorld tx) terminal := by
  simp only [interpretConstructor, raw, Bool.false_eq_true, ↓reduceIte, bound, body]

/-- Actual terminal exception from the supplied body frame, with rollback. -/
theorem function_helpers_exception
    (spec : CompilationModel) (fn : FunctionSpec)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (terminal : RuntimeState)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (body : execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := withTransactionContext initialWorld tx, bindings := bindings,
          selector := tx.functionSelector, externalCallOracle := oracle,
          executionContext := context, externalCallIndex := index, errors := spec.errors } fn.body = .exceptional terminal) :
    interpretFunctionWithHelpers spec fuel fn tx initialWorld oracle context index =
      exceptionalResult spec (withTransactionContext initialWorld tx) terminal := by
  simp only [interpretFunctionWithHelpers, bound, body]

/-- Actual terminal exception from the supplied body frame, with rollback. -/
theorem constructor_helpers_exception
    (spec : CompilationModel) (ctor : ConstructorSpec)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (terminal : RuntimeState)
    (raw : constructorTouchesUnsupportedRawCalldataSurface spec ctor = false)
    (bound : constructorExecutionBindings ctor tx.args = some bindings)
    (body : execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := withTransactionContext initialWorld tx, bindings := bindings,
          selector := tx.functionSelector, externalCallOracle := oracle,
          executionContext := context, externalCallIndex := index } ctor.body = .exceptional terminal) :
    interpretConstructorWithHelpers spec fuel ctor tx initialWorld oracle context index =
      exceptionalResult spec (withTransactionContext initialWorld tx) terminal := by
  simp only [interpretConstructorWithHelpers, raw, Bool.false_eq_true, ↓reduceIte, bound, body]

/-- Selector dispatch forwards the supplied context and external schedule. -/
theorem dispatch
    (spec : CompilationModel) (selectors : List Nat) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (selected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (payable : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false) :
    interpretContract spec selectors tx initialWorld oracle context index =
      interpretFunction spec fn tx initialWorld oracle context index := by
  simp only [interpretContract, selected, payable, Bool.false_eq_true, ↓reduceIte]

/-- Selector dispatch forwards the supplied context and external schedule. -/
theorem dispatch_helpers
    (spec : CompilationModel) (selectors : List Nat) (fn : FunctionSpec)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (selected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (payable : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false) :
    interpretContractWithHelpers spec selectors fuel tx initialWorld oracle context index =
      interpretFunctionWithHelpers spec fuel fn tx initialWorld oracle context index := by
  simp only [interpretContractWithHelpers, selected, payable, Bool.false_eq_true, ↓reduceIte]

end Compiler.Proofs.IRGeneration.SourcePublicContextLaws
