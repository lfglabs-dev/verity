import Compiler.Proofs.IRGeneration.PublicResultBridge
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryTrace
import Compiler.Proofs.IRGeneration.GenericInduction.Helpers

/-! Contextual public body execution, separate from ordinary EVM certification.
The generic witness can admit actual interpreter refusals or exceptions. This
module transports those outcomes without asserting that they are ordinary. -/
namespace Compiler.Proofs.IRGeneration
open Compiler CompilationModel Yul

/-- The public function really executes with the supplied oracle, cursor and
context. Generic induction supplies operational correspondence at that same
state; no missing ordinary-outcome premise is silently discharged here. -/
theorem contextual_public_body_outcome
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (state : IRState) (extraFuel : Nat)
    (noEvents : model.events = [])
    (bound : SourceSemantics.bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (generic : StmtListGenericCore (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (compiled : compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (scope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (bounded : FunctionBody.bindingsBounded bindings)
    (exactVars : FunctionBody.bindingsExactlyMatchIRVarsOnScope (fn.params.map (·.name)) bindings state)
    (aligned : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx,
        bindings := bindings, selector := tx.functionSelector,
        externalCallOracle := oracle, executionContext := context,
        externalCallIndex := index, errors := model.errors } state) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx,
          bindings := bindings, selector := tx.functionSelector,
          externalCallOracle := oracle, executionContext := context,
          externalCallIndex := index, errors := model.errors } fn.body = sourceResult ∧
      SourceSemantics.interpretFunction model fn tx initialWorld oracle context index =
        FunctionBody.stmtResultToSourceResult model
          (SourceSemantics.withTransactionContext initialWorld tx) sourceResult ∧
      execIRStmts (sizeOf bodyStmts + extraFuel + 1) state bodyStmts = irExec ∧
      stmtOutcomeMatchesIRExec (SourceSemantics.effectiveFields model) sourceResult irExec := by
  let runtime : SourceSemantics.RuntimeState :=
    { world := SourceSemantics.withTransactionContext initialWorld tx,
      bindings := bindings, selector := tx.functionSelector,
      externalCallOracle := oracle, executionContext := context,
      externalCallIndex := index, errors := model.errors }
  obtain ⟨bodyIR, compileOk, related⟩ := exec_compileStmtList_generic_sizeOf_extraFuel
    (fields := SourceSemantics.effectiveFields model) (runtime := runtime)
    (state := state) (scope := fn.params.map (·.name)) (stmts := fn.body)
    (extraFuel := extraFuel) generic scope exactVars bounded aligned
  have sameBody : bodyIR = bodyStmts := Except.ok.inj (compileOk.symm.trans compiled)
  subst bodyIR
  refine ⟨SourceSemantics.execStmtList (SourceSemantics.effectiveFields model) runtime fn.body,
    _, rfl, ?_, rfl, related⟩
  apply public_function_body_result model fn tx initialWorld oracle context index bindings _ bound
  simp only [noEvents, SourceSemantics.execStmtListWithEvents_nil_eq_execStmtList, runtime]

/-- Ordinary public certification additionally consumes a compositional trace
of actual admitted Source steps. The operational theorem remains available for
exceptions and refusals; neither class is relabeled by this corollary. -/
theorem contextual_public_body_certified
    (model : CompilationModel) (fn : FunctionSpec) (bodyStmts : List YulStmt)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (state : IRState) (extraFuel : Nat)
    (noEvents : model.events = [])
    (bound : SourceSemantics.bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (generic : StmtListGenericCore (SourceSemantics.effectiveFields model)
      (fn.params.map (·.name)) fn.body)
    (compiled : compileStmtList (SourceSemantics.effectiveFields model) [] [] .calldata [] false
      (fn.params.map (·.name)) [] fn.body = Except.ok bodyStmts)
    (scope : FunctionBody.scopeNamesPresent (fn.params.map (·.name)) bindings)
    (bounded : FunctionBody.bindingsBounded bindings)
    (exactVars : FunctionBody.bindingsExactlyMatchIRVarsOnScope (fn.params.map (·.name)) bindings state)
    (aligned : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx,
        bindings := bindings, selector := tx.functionSelector,
        externalCallOracle := oracle, executionContext := context,
        externalCallIndex := index, errors := model.errors } state)
    (admitted : OrdinarySourceTrace (SourceSemantics.effectiveFields model)
      { world := SourceSemantics.withTransactionContext initialWorld tx,
        bindings := bindings, selector := tx.functionSelector,
        externalCallOracle := oracle, executionContext := context,
        externalCallIndex := index, errors := model.errors } fn.body) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmtList (SourceSemantics.effectiveFields model)
        { world := SourceSemantics.withTransactionContext initialWorld tx,
          bindings := bindings, selector := tx.functionSelector,
          externalCallOracle := oracle, executionContext := context,
          externalCallIndex := index, errors := model.errors } fn.body = sourceResult ∧
      SourceSemantics.interpretFunction model fn tx initialWorld oracle context index =
        FunctionBody.stmtResultToSourceResult model
          (SourceSemantics.withTransactionContext initialWorld tx) sourceResult ∧
      execIRStmts (sizeOf bodyStmts + extraFuel + 1) state bodyStmts = irExec ∧
      FunctionBody.stmtResultMatchesIRExec (SourceSemantics.effectiveFields model) sourceResult irExec := by
  obtain ⟨sourceResult, irExec, executed, projected, irExecuted, related⟩ :=
    contextual_public_body_outcome model fn bodyStmts tx initialWorld oracle
      context index bindings state extraFuel noEvents bound generic compiled
      scope bounded exactVars aligned
  refine ⟨sourceResult, irExec, executed, projected, irExecuted, ?_⟩
  apply (stmtOutcomeMatchesIRExec_certified_iff _ _ _).mpr
  refine ⟨related, ?_⟩
  rw [← executed]
  exact admitted.outcome_is_ordinary

end Compiler.Proofs.IRGeneration
