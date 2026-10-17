import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel SourceSemantics

/-- Package helper-aware IR outcomes with exactly the ordinary certificate.
Exceptions, refusals and LEAVE cannot acquire this certificate. -/
theorem helper_body_result_matches
    (spec : CompilationModel) (fields : List Field)
    (initialWorld : Verity.ContractState) (rollback : IRState)
    (source : StmtResult) (ir : IRExecResultWithInternals)
    (storage : rollback.storage = fun s => IRStorageWord.ofNat
      (encodeStorage spec initialWorld s.toNat))
    (events : rollback.events = encodeEvents initialWorld.events)
    (fieldEq : fields = effectiveFields spec)
    (matched : stmtResultMatchesIRExecWithInternals fields source ir) :
    FunctionBody.sourceResultMatchesIRResult
      (FunctionBody.stmtResultToSourceResult spec initialWorld source)
      (FunctionBody.irResultOfExecResultWithInternals rollback ir) := by
  cases ir <;> first
    | exact FunctionBody.stmtResultToSourceResult_matches_irExecResult
        spec fields initialWorld rollback source _ storage events fieldEq matched
    | contradiction

/-- Actual public entry executes at the declared error table and supplied
context/oracle/cursor. This equation does not authenticate those inputs. -/
theorem public_function_body_result
    (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (cursor : Nat)
    (bindings : List (String × Nat)) (source : StmtResult)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithEvents (effectiveFields spec) spec.events
      { world := withTransactionContext initialWorld tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle,
        executionContext := context, externalCallIndex := cursor, errors := spec.errors } fn.body = source) :
    interpretFunction spec fn tx initialWorld oracle context cursor =
      FunctionBody.stmtResultToSourceResult spec (withTransactionContext initialWorld tx) source := by
  simp only [interpretFunction, bound, executed]
  cases source <;> rfl

/-- Helper public entry uses the same actual body frame and rollback world. -/
theorem public_helper_function_body_result
    (spec : CompilationModel) (fn : FunctionSpec) (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (cursor : Nat)
    (bindings : List (String × Nat)) (source : StmtResult)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithHelpers spec (effectiveFields spec) fuel
      { world := withTransactionContext initialWorld tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle,
        executionContext := context, externalCallIndex := cursor, errors := spec.errors } fn.body = source) :
    interpretFunctionWithHelpers spec fuel fn tx initialWorld oracle context cursor =
      FunctionBody.stmtResultToSourceResult spec (withTransactionContext initialWorld tx) source := by
  simp only [interpretFunctionWithHelpers, bound, executed]
  cases source <;> rfl

end Compiler.Proofs.IRGeneration
