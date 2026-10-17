import Compiler.Proofs.IRGeneration.SourceSemantics

namespace Compiler.Proofs.IRGeneration.SourceErrorDeclarations
open Compiler.CompilationModel SourceSemantics

/-- Every carried execution state retains the caller's declared errors.
Payload-only/refused results carry no continuation state. -/
def Preserves (errors : List ErrorDef) : StmtResult → Prop
  | .continue next | .stop next | .return _ next | .exceptional next => next.errors = errors
  | .revert | .revertWithData _ | .interpretationError _ => True

theorem copy_errors (state : RuntimeState) (destination source size : Nat)
    (errorPrefix : String := "") :
    Preserves state.errors (execReturndataCopy state destination source size errorPrefix) := by
  unfold execReturndataCopy
  cases Verity.Core.Model.ReturndataCopy.run state.world state.executionContext destination source size <;>
    first | rfl | trivial

theorem forEach_errors (name : String) (runBody : RuntimeState → StmtResult)
    (body : ∀ state, Preserves state.errors (runBody state))
    (state : RuntimeState) (index remaining : Nat) :
    Preserves state.errors (execForEachLoop name runBody state index remaining) := by
  induction remaining generalizing state index with
  | zero => rfl
  | succ remaining ih =>
      let loopState := { state with bindings := bindValue state.bindings name (wordNormalize index) }
      have kept := body loopState
      simp only [loopState] at kept
      cases result : runBody { state with bindings := bindValue state.bindings name (wordNormalize index) } <;>
        simp only [result, Preserves] at kept
      all_goals simp only [execForEachLoop, result, Preserves]
      all_goals try first | exact True.intro | exact kept
      rename_i next
      have tail := ih next (index + 1)
      simpa only [kept, Preserves] using tail

theorem setBit_errors (name : String) (runBody : RuntimeState → StmtResult)
    (body : ∀ state, Preserves state.errors (runBody state))
    (fuel : Nat) (state : RuntimeState) (bitmap : Nat) :
    Preserves state.errors (execForEachSetBitLoop name runBody fuel state bitmap) := by
  induction fuel generalizing state bitmap with
  | zero => rfl
  | succ fuel ih =>
      by_cases zero : bitmap = 0
      · simp [execForEachSetBitLoop, zero, Preserves]
      · let loopState := { state with bindings := bindValue state.bindings name (wordNormalize (msbIndex bitmap)) }
        have kept := body loopState
        simp only [loopState] at kept
        cases result : runBody { state with bindings := bindValue state.bindings name (wordNormalize (msbIndex bitmap)) } <;>
          simp only [result, Preserves] at kept
        all_goals simp only [execForEachSetBitLoop, zero, if_false, result, Preserves]
        all_goals try first | exact True.intro | exact kept
        rename_i next
        have tail := ih next (clearMsb bitmap)
        simpa only [kept, Preserves] using tail

theorem forEach_aligned_errors (errors : List ErrorDef) (name : String) (runBody : RuntimeState → StmtResult)
    (body : ∀ state, state.errors = errors → Preserves state.errors (runBody state))
    (state : RuntimeState) (index remaining : Nat) (aligned : state.errors = errors) :
    Preserves state.errors (execForEachLoop name runBody state index remaining) := by
  induction remaining generalizing state index with
  | zero => rfl
  | succ remaining ih =>
      let loopState := { state with bindings := bindValue state.bindings name (wordNormalize index) }
      have kept := body loopState aligned
      simp only [loopState] at kept
      cases result : runBody { state with bindings := bindValue state.bindings name (wordNormalize index) } <;>
        simp only [result, Preserves] at kept
      all_goals simp only [execForEachLoop, result, Preserves]
      all_goals try first | exact True.intro | exact kept
      rename_i next
      have tail := ih next (index + 1) (kept.trans aligned)
      simpa only [kept, Preserves] using tail

theorem setBit_aligned_errors (errors : List ErrorDef) (name : String) (runBody : RuntimeState → StmtResult)
    (body : ∀ state, state.errors = errors → Preserves state.errors (runBody state))
    (fuel : Nat) (state : RuntimeState) (bitmap : Nat) (aligned : state.errors = errors) :
    Preserves state.errors (execForEachSetBitLoop name runBody fuel state bitmap) := by
  induction fuel generalizing state bitmap with
  | zero => rfl
  | succ fuel ih =>
      by_cases zero : bitmap = 0
      · simp [execForEachSetBitLoop, zero, Preserves]
      · let loopState := { state with bindings := bindValue state.bindings name (wordNormalize (msbIndex bitmap)) }
        have kept := body loopState aligned
        simp only [loopState] at kept
        cases result : runBody { state with bindings := bindValue state.bindings name (wordNormalize (msbIndex bitmap)) } <;>
          simp only [result, Preserves] at kept
        all_goals simp only [execForEachSetBitLoop, zero, if_false, result, Preserves]
        all_goals try first | exact True.intro | exact kept
        rename_i next
        have tail := ih next (clearMsb bitmap) (kept.trans aligned)
        simpa only [kept, Preserves] using tail

mutual
  theorem statement_errors (fields : List Field) (state : RuntimeState) (stmt : Stmt) :
      Preserves state.errors (execStmt fields state stmt) := by
    cases stmt with
    | ite cond yes no =>
        simp only [execStmt]
        split
        · split
          · exact list_errors fields state yes
          · exact list_errors fields state no
        · trivial
    | forEach name count body =>
        simp only [execStmt]
        split
        · exact forEach_errors name (fun next => execStmtList fields next body)
            (fun next => list_errors fields next body) _ _ _
        · trivial
    | forEachSetBit name bitmap body =>
        simp only [execStmt]
        split
        · exact setBit_errors name (fun next => execStmtList fields next body)
            (fun next => list_errors fields next body) _ _ _
        · trivial
    | _ =>
        simp only [execStmt, typedErrorRevertResult, execCreation]
        all_goals repeat' first | split | (solve | simp_all [Preserves]) | (solve | apply copy_errors)
  theorem list_errors (fields : List Field) (state : RuntimeState) (stmts : List Stmt) :
      Preserves state.errors (execStmtList fields state stmts) := by
    cases stmts with
    | nil => rfl
    | cons stmt rest =>
        have kept := statement_errors fields state stmt
        cases result : execStmt fields state stmt <;> simp only [result, Preserves] at kept
        all_goals simp only [execStmtList, result, Preserves]
        all_goals try first | exact True.intro | exact kept
        rename_i next
        have tail := list_errors fields next rest
        simpa only [kept, Preserves] using tail
end

private theorem failed_errors (errors : List ErrorDef) (result : InternalFunctionResult)
    (kept : ∀ terminal, result.exceptionalState = some terminal → terminal.errors = errors) :
    Preserves errors (failedInternalOutcome result) := by
  unfold failedInternalOutcome
  split
  · trivial
  · split
    · rename_i terminal hterminal
      exact kept terminal hterminal
    · trivial

mutual
  theorem helper_statement_errors (spec : CompilationModel) (fields : List Field) (fuel : Nat) (state : RuntimeState) (stmt : Stmt)
      (aligned : state.errors = spec.errors) :
      Preserves state.errors (execStmtWithHelpers spec fields fuel state stmt) := by
    cases stmt with
    | ite cond yes no =>
        simp only [execStmtWithHelpers]
        split
        · split
          · exact helper_list_errors spec fields fuel state yes aligned
          · exact helper_list_errors spec fields fuel state no aligned
        · trivial
    | forEach name count body =>
        simp only [execStmtWithHelpers]
        split
        · exact forEach_aligned_errors spec.errors name (fun next => execStmtListWithHelpers spec fields fuel next body)
            (fun next h => helper_list_errors spec fields fuel next body h) _ _ _ aligned
        · trivial
    | forEachSetBit name bitmap body =>
        simp only [execStmtWithHelpers]
        split
        · exact setBit_aligned_errors spec.errors name (fun next => execStmtListWithHelpers spec fields fuel next body)
            (fun next h => helper_list_errors spec fields fuel next body h) _ _ _ aligned
        · trivial
    | internalCall name args =>
        cases fuel <;> simp only [execStmtWithHelpers]
        all_goals repeat' first | split | (solve | simp_all [Preserves]) | (solve | apply failed_errors; intro terminal hterminal; exact (internal_exception_errors spec _ _ _ _ _ _ _ terminal hterminal).trans aligned.symm)
    | internalCallAssign names name args =>
        cases fuel <;> simp only [execStmtWithHelpers]
        all_goals repeat' first | split | (solve | simp_all [Preserves]) | (solve | apply failed_errors; intro terminal hterminal; exact (internal_exception_errors spec _ _ _ _ _ _ _ terminal hterminal).trans aligned.symm)
    | _ =>
        simp only [execStmtWithHelpers, typedErrorRevertResult, execCreation]
        all_goals repeat' first | split | (solve | simp_all [Preserves]) | (solve | apply copy_errors)
  termination_by (fuel, sizeOf stmt)
  decreasing_by all_goals (simp_wf; omega)
  theorem helper_list_errors (spec : CompilationModel) (fields : List Field) (fuel : Nat) (state : RuntimeState) (stmts : List Stmt)
      (aligned : state.errors = spec.errors) :
      Preserves state.errors (execStmtListWithHelpers spec fields fuel state stmts) := by
    cases stmts with
    | nil => simp [execStmtListWithHelpers, Preserves]
    | cons stmt rest =>
        have kept := helper_statement_errors spec fields fuel state stmt aligned
        cases result : execStmtWithHelpers spec fields fuel state stmt <;> simp only [result, Preserves] at kept
        all_goals simp only [execStmtListWithHelpers, result, Preserves]
        all_goals try first | exact True.intro | exact kept
        rename_i next
        have tail := helper_list_errors spec fields fuel next rest (kept.trans aligned)
        simpa only [kept, Preserves] using tail
  termination_by (fuel, sizeOf stmts)
  decreasing_by all_goals (simp_wf; omega)
  theorem internal_exception_errors (spec : CompilationModel) (fuel : Nat)
      (fn : FunctionSpec) (world : Verity.ContractState) (args : List Nat)
      (oracle : Nat → ExternalCallOutcome) (cursor : Nat)
      (context : Option Verity.Core.Model.ExecutionContext) (terminal : RuntimeState)
      (executed : (interpretInternalFunctionFuel spec fuel fn world args oracle cursor context).exceptionalState = some terminal) :
      terminal.errors = spec.errors := by
    unfold interpretInternalFunctionFuel at executed
    split at executed
    · simp [revertedInternalResult] at executed
    · rename_i bindings hbindings
      have kept := helper_list_errors spec (effectiveFields spec) fuel
        { world := world, bindings := bindings, externalCallOracle := oracle,
          externalCallIndex := cursor, executionContext := context, errors := spec.errors } fn.body rfl
      cases outcome : execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := world, bindings := bindings, externalCallOracle := oracle,
          externalCallIndex := cursor, executionContext := context, errors := spec.errors } fn.body <;>
        simp only [outcome] at executed kept
      all_goals simp [successInternalResult, revertedInternalResult, exceptionalInternalResult] at executed
      subst terminal
      exact kept
  termination_by (fuel, sizeOf fn.body + 1)
  decreasing_by all_goals omega

end

theorem helper_continuation_declarations (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (state next : RuntimeState) (body : List Stmt)
    (aligned : state.errors = spec.errors)
    (executed : execStmtListWithHelpers spec fields fuel state body = .continue next) :
    next.errors = spec.errors := by
  have kept := helper_list_errors spec fields fuel state body aligned
  simpa only [executed, Preserves, aligned] using kept

/-- The actual function-entry declaration assignment is retained for every
carried body result, including early return, stop and exceptional creation. -/
theorem function_entry_declarations (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (world : Verity.ContractState) (bindings : List (String × Nat))
    (selector : Nat) (oracle : Nat → ExternalCallOutcome) (body : List Stmt) :
    Preserves spec.errors (execStmtListWithHelpers spec fields fuel
      { world := world, bindings := bindings, selector := selector,
        externalCallOracle := oracle, errors := spec.errors } body) :=
  helper_list_errors spec fields fuel _ body rfl

end Compiler.Proofs.IRGeneration.SourceErrorDeclarations
