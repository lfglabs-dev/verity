import Compiler.Proofs.IRGeneration.HelperBodyShape
import Compiler.Proofs.IRGeneration.InternalHelperBodyCorrespondence

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel
open Compiler.Yul

def internalHelperBodyIRExecResultAsCallResult
    (callerState : IRState) (helper : IRInternalFunctionDef) :
    IRExecResultWithInternals → IRValuesEvalResult
  | .continue finalState =>
      .values (internalReturnValues finalState helper.rets)
        (restoreCallerVars callerState finalState)
  | .leave finalState =>
      .values (internalReturnValues finalState helper.rets)
        (restoreCallerVars callerState finalState)
  | .stop finalState =>
      .stop (restoreCallerVars callerState finalState)
  | .return value finalState =>
      .return value (restoreCallerVars callerState finalState)
  | .revert _ =>
      .revert callerState

/-- N1a helper-body bridge: executing the compiled helper through
`execIRInternalFunctionWithInternals` unfolds to the helper-body execution that
is matched by `internal_helper_body_exec_matches...`, and the projected source
helper result satisfies the real internal-helper summary contract.

The execution equation intentionally leaves `.stop` and `.return` propagation
visible.  Callers that need ordinary helper return values must combine this with
the existing stop/return-family exclusions for the helper body. -/
theorem execIRInternalFunctionWithInternals_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {args : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length) :
    (execIRInternalFunctionWithInternals runtimeContract
        (sizeOf helper.body + extraFuel + 1 + 1) callerState helper args =
      internalHelperBodyIRExecResultAsCallResult callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel))
    ∧
      summary.post helperFuel initialWorld args
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).success
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).returnValue
        (internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).world := by
  rcases internal_helper_body_exec_matches_entryBindings_and_projected_result_of_bindInternalArgs_and_generic
      (runtimeContract := runtimeContract) (spec := spec) (callee := callee)
      (helper := helper) (callerState := callerState)
      (initialWorld := initialWorld) (args := args)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      helperFuel extraFuel hfuelPos ctx with
    ⟨_hmatch, hinterp⟩
  constructor
  · have hsourceLen : callee.params.length = args.length :=
      bindInternalArgs_length_eq_of_some ctx.bindArgs
    have hlen : helper.params.length = args.length := harity.trans hsourceLen
    rw [execIRInternalFunctionWithInternals_succ_of_params_match
      runtimeContract (sizeOf helper.body + extraFuel + 1)
      callerState helper args hlen]
    rfl
  · have hpost := hsound helperFuel initialWorld args
    simpa [hinterp] using hpost

private theorem internalFunctionYulName_head (calleeName : String) :
    (CompilationModel.internalFunctionYulName calleeName).toList.head? = some 'i' := by
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix]
  decide

private theorem internalFunctionYulName_ne_of_head
    (calleeName builtinName : String)
    (hhead : builtinName.toList.head? ≠ some 'i') :
    CompilationModel.internalFunctionYulName calleeName ≠ builtinName := by
  intro hEq
  have hHead := congrArg (fun s : String => s.toList.head?) hEq
  change (CompilationModel.internalFunctionYulName calleeName).toList.head? =
    builtinName.toList.head? at hHead
  rw [internalFunctionYulName_head calleeName] at hHead
  exact hhead hHead.symm

private theorem internalFunctionYulName_isYulLogName_false (calleeName : String) :
    isYulLogName (CompilationModel.internalFunctionYulName calleeName) = false := by
  simp [isYulLogName,
    internalFunctionYulName_ne_of_head calleeName "log0" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log1" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log2" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log3" (by decide),
    internalFunctionYulName_ne_of_head calleeName "log4" (by decide)]

noncomputable abbrev internalHelperCallFuel
    (helper : IRInternalFunctionDef) (extraFuel : Nat) : Nat :=
  sizeOf helper.body + extraFuel + 1 + 1

abbrev internalHelperSummaryPostAt
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState)
    (entryBindings : List (String × Nat))
    (helperFuel : Nat) (args : List Nat)
    (summary : InternalHelperSummaryContract) : Prop :=
  summary.post helperFuel initialWorld args
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).success
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).returnValue
    (internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)).world

abbrev internalHelperAssignCallResult
    (names : List String) (callerState : IRState) (helper : IRInternalFunctionDef)
    (bodyResult : IRExecResultWithInternals) : IRExecResultWithInternals :=
  match internalHelperBodyIRExecResultAsCallResult callerState helper bodyResult with
  | .values values state' =>
      if names.length = values.length then
        .continue (state'.setVars (names.zip values))
      else .revert state'
  | .stop state' => .stop state'
  | .return value state' => .return value state'
  | .revert state' => .revert state'

private theorem execIRStmtsWithInternals_singleton_expr_internalFunctionYulName_call_internal
    (runtimeContract : IRContract) (fuel : Nat) (state : IRState)
    (calleeName : String) (argExprs : List YulExpr)
    (helper : IRInternalFunctionDef) (args : List Nat) (callerState : IRState)
    (hargs : evalIRExprsWithInternals runtimeContract (fuel + 1) state argExprs =
      .values args callerState)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper) :
    execIRStmtsWithInternals runtimeContract (fuel + 3) state
      [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      match execIRInternalFunctionWithInternals runtimeContract fuel
          callerState helper args with
      | .values _ state' => .continue state'
      | .stop state' => .stop state'
      | .return value state' => .return value state'
      | .revert state' => .revert state' := by
  exact execIRStmtsWithInternals_singleton_expr_call_internal
    runtimeContract fuel state
    (CompilationModel.internalFunctionYulName calleeName) argExprs helper args callerState
    hargs hfind
    (internalFunctionYulName_ne_of_head calleeName "stop" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "sstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "mstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "tstore" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "revert" (by decide))
    (internalFunctionYulName_ne_of_head calleeName "return" (by decide))
    (internalFunctionYulName_isYulLogName_false calleeName)

/-- N2/N3 assignment-call instantiation of the N1a helper-summary bridge.
This is the singleton `letMany (.call internal_helper ...)` wrapper around
`execIRInternalFunctionWithInternals_obeys_internal_helper_summary`. -/
theorem execIRStmtsWithInternals_internalCallAssign_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {state callerState : IRState} {initialWorld : Verity.ContractState}
    {names : List String} {calleeName : String}
    {argExprs : List YulExpr} {args : List Nat}
    {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hargs : evalIRExprsWithInternals runtimeContract
      (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values args callerState) :
    (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.letMany names
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      internalHelperAssignCallResult names callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel))
    ∧
      internalHelperSummaryPostAt spec callee initialWorld entryBindings
        helperFuel args summary := by
  have hsummary := execIRInternalFunctionWithInternals_obeys_internal_helper_summary
    (runtimeContract := runtimeContract) (spec := spec) (callee := callee) (helper := helper)
    (callerState := callerState) (initialWorld := initialWorld) (args := args)
    (sourceBindings := sourceBindings) (entryBindings := entryBindings) (summary := summary)
    helperFuel extraFuel hfuelPos ctx hsound harity
  constructor
  · rw [execIRStmtsWithInternals_singleton_letMany_call_internal
      runtimeContract (internalHelperCallFuel helper extraFuel) state names
      (CompilationModel.internalFunctionYulName calleeName) argExprs helper args
      callerState hargs hfind]
    rw [show internalHelperCallFuel helper extraFuel =
      sizeOf helper.body + extraFuel + 1 + 1 from rfl, hsummary.1]
    simp [internalHelperAssignCallResult]
    cases internalHelperBodyIRExecResultAsCallResult callerState helper
      (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) <;> rfl
  · exact hsummary.2

/-- N2/N3 void-call instantiation of the N1a helper-summary bridge.  The normal
helper values are discarded by `exprStmt`, while stop/return/revert propagation
remains explicit. -/
theorem execIRStmtsWithInternals_internalCall_obeys_internal_helper_summary
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {state callerState : IRState} {initialWorld : Verity.ContractState}
    {calleeName : String} {argExprs : List YulExpr} {args : List Nat}
    {sourceBindings entryBindings : List (String × Nat)}
    {summary : InternalHelperSummaryContract}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel)
    (hsound : SourceSemantics.InternalHelperSummarySound spec callee summary)
    (harity : helper.params.length = callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hargs : evalIRExprsWithInternals runtimeContract
      (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values args callerState) :
    (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.exprStmt
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] =
      match internalHelperBodyIRExecResultAsCallResult callerState helper
          (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) with
      | .values _ state' => IRExecResultWithInternals.continue state'
      | .stop state' => IRExecResultWithInternals.stop state'
      | .return value state' => IRExecResultWithInternals.return value state'
      | .revert state' => IRExecResultWithInternals.revert state')
    ∧
      internalHelperSummaryPostAt spec callee initialWorld entryBindings
        helperFuel args summary := by
  have hsummary :=
    execIRInternalFunctionWithInternals_obeys_internal_helper_summary
      (runtimeContract := runtimeContract) (spec := spec) (callee := callee)
      (helper := helper) (callerState := callerState)
      (initialWorld := initialWorld) (args := args)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      (summary := summary) helperFuel extraFuel hfuelPos ctx hsound harity
  constructor
  · rw [execIRStmtsWithInternals_singleton_expr_internalFunctionYulName_call_internal
      runtimeContract (internalHelperCallFuel helper extraFuel) state
      calleeName argExprs helper args callerState hargs hfind]
    rw [show internalHelperCallFuel helper extraFuel =
      sizeOf helper.body + extraFuel + 1 + 1 from rfl]
    rw [hsummary.1]
  · exact hsummary.2

/-- Concrete regression for the rank-0 void-helper body-shape seam: an empty
helper body is unaffected by internal return targets. -/
theorem empty_void_helper_body_compile_shape_irrelevant_regression :
    CompilationModel.compileStmtListWithFork [] [] [] .calldata
      ([] : List String) true ([] : List String) []
      Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] =
    CompilationModel.compileStmtListWithFork [] [] [] .calldata
      [] false [] [] Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] := by
  exact
    compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
      [] [] [] .calldata ([] : List String) true ([] : List String) []
      Verity.Core.Intrinsics.HardFork.cancun ([] : List Stmt) [] rfl

/-- Regression: a helper that delegates to another helper is not accepted by the
local stop-free boundary without a transitive no-stop summary for the callee. -/
theorem stmtListUsesStop_rejects_statement_internal_helper_call_regression :
    stmtListUsesStop [Stmt.internalCall "stoppingHelper" []] = true := by
  unfold stmtListUsesStop Stmt.anyDeepList
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  unfold Stmt.anyDeep
  simp [stmtUsesStopBoundaryNode, Stmt.childLists]

/-- Regression: expression-position helper calls are also rejected by the local
stop-free boundary. -/
theorem stmtListUsesStop_rejects_expression_internal_helper_call_regression :
    stmtListUsesStop
      [Stmt.letVar "value" (Expr.internalCall "stoppingHelper" [])] = true := by
  unfold stmtListUsesStop Stmt.anyDeepList
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  unfold Stmt.anyDeep
  simp only [Stmt.childLists, List.attach_nil, List.any_nil, Bool.or_false]
  unfold stmtUsesStopBoundaryNode
  simp only [Stmt.directMetadata, List.any_cons, List.any_nil, Bool.or_false]
  unfold exprUsesInternalHelperCall Expr.anyDeep
  simp only [exprUsesInternalHelperCallNode, Expr.children, List.attach_nil, List.any_nil,
    Bool.or_false]

end Compiler.Proofs.IRGeneration
