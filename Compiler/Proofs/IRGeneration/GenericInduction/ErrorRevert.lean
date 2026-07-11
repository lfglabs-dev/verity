import Compiler.Proofs.IRGeneration.GenericInduction.ExprStmt

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

private theorem compiledStmtStep_requireError_revert_case
    {spec : CompilationModel} {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {scope : List String} {helperFuel extraFuel : Nat} {cond : Expr}
    {errorName : String} {args : List Expr} {failCond : YulExpr} {revertStmts : List YulStmt}
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some 0)
    (hfailEval : evalIRExpr state failCond = some 1)
    (hrevertExec : ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next) :
    ∃ sourceResult irResult,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (.requireError cond errorName args) = sourceResult ∧
      execIRStmts ([YulStmt.if_ failCond revertStmts].length + extraFuel + 1) state
        [YulStmt.if_ failCond revertStmts] = irResult ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond errorName args))
        sourceResult irResult := by
  rcases hrevertExec state extraFuel with ⟨revState, hrev⟩
  have hstmt : execIRStmt (extraFuel + 1) state (YulStmt.if_ failCond revertStmts) =
      .revert revState := by
    simp [execIRStmt, hfailEval, hrev]
  have hIRExec : execIRStmts (1 + extraFuel + 1) state
      [YulStmt.if_ failCond revertStmts] = .revert revState := by
    have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
    rw [this]
    simp [execIRStmts, hstmt]
  have hSrcExec : SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
      (.requireError cond errorName args) = .revert := by
    simp [SourceSemantics.execStmtWithHelpers, SourceSemantics.typedErrorRevertResult, hCondSrc]
  refine ⟨.revert, .revert revState, hSrcExec, ?_, ?_⟩
  · simpa using hIRExec
  · simp [stmtStepMatchesIRExec]

private theorem compiledStmtStep_requireError_continue_case
    {spec : CompilationModel} {fields : List Field} {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState} {helperFuel extraFuel condVal : Nat} {cond : Expr} {errorName : String}
    {args : List Expr} {failCond : YulExpr} {revertStmts : List YulStmt}
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hzero : condVal ≠ 0)
    (hfailEval : evalIRExpr state failCond = some 0)
    (hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
      (stmtNextScope scope (.requireError cond errorName args)) runtime.bindings state)
    (hscope' : FunctionBody.scopeNamesPresent
      (stmtNextScope scope (.requireError cond errorName args)) runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ sourceResult irResult,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (.requireError cond errorName args) = sourceResult ∧
      execIRStmts ([YulStmt.if_ failCond revertStmts].length + extraFuel + 1) state
        [YulStmt.if_ failCond revertStmts] = irResult ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond errorName args))
        sourceResult irResult := by
  have hstmt : execIRStmt (extraFuel + 1) state (YulStmt.if_ failCond revertStmts) =
      .continue state := by
    simp [execIRStmt, hfailEval]
  have hIRExec : execIRStmts (1 + extraFuel + 1) state
      [YulStmt.if_ failCond revertStmts] = .continue state := by
    have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
    rw [this]
    simp [execIRStmts, hstmt]
  have hSrcExec : SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
      (.requireError cond errorName args) = .continue runtime := by
    simp [SourceSemantics.execStmtWithHelpers, hCondSrc, hzero]
  refine ⟨.continue runtime, .continue state, hSrcExec, ?_, ?_⟩
  · simpa using hIRExec
  · simp [stmtStepMatchesIRExec]
    exact ⟨hruntime, hexact', hbounded, hscope'⟩

private def compiledStmtStep_requireError_impl
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {errorName : String}
    {args : List Expr}
    {failCond : YulExpr}
    {revertStmts : List YulStmt}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hnextScopeIncl :
      FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (.requireError cond errorName args)) scope)
    (hfailCompile :
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (.requireError cond errorName args) =
          Except.ok [YulStmt.if_ failCond revertStmts])
    (hrevertExec :
      ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next) :
    CompiledStmtStepWithHelpers spec fields scope (.requireError cond errorName args)
      [YulStmt.if_ failCond revertStmts] where
  compileOk := hcompile
  preserves runtime state helperFuel extraFuel hexact hscope hbounded hruntime hslack := by
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    rcases FunctionBody.eval_compileRequireFailCond_core_of_scope
        hcore hexact hinScope hbounded hpresent hruntime with
      ⟨failCond', hfailCompile', hfailEval⟩
    rw [hfailCompile] at hfailCompile'
    injection hfailCompile' with hfailEq
    subst hfailEq
    have hCondEval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded hpresent hruntime
    rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with ⟨condIR, hcondIR⟩
    rw [hcondIR] at hCondEval
    simp [Except.toOption] at hCondEval
    rcases hCondIRVal : evalIRExpr state condIR with _ | condVal
    · simp [hCondIRVal, Option.bind] at hCondEval
    · simp [hCondIRVal, Option.bind] at hCondEval
      have hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal :=
        hCondEval.symm
      by_cases hzero : condVal = 0
      · have hCondZero : SourceSemantics.evalExpr fields runtime cond = some 0 := by
          rw [hCondSrc, hzero]
        have hfailEval' : evalIRExpr state failCond = some 1 := by
          rw [hCondSrc, hzero] at hfailEval
          simpa [SourceSemantics.boolWord] using hfailEval
        simpa using compiledStmtStep_requireError_revert_case
          (spec := spec) (fields := fields) (runtime := runtime) (state := state)
          (helperFuel := helperFuel) (extraFuel := extraFuel) (cond := cond)
          (errorName := errorName) (args := args) (failCond := failCond)
          (revertStmts := revertStmts) hCondZero hfailEval' hrevertExec
      · have hfailEval' : evalIRExpr state failCond = some 0 := by
          have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
            rw [hCondSrc]
            simp [hzero]
          simpa [this, SourceSemantics.boolWord] using hfailEval
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.requireError cond errorName args)) runtime.bindings state :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hnextScopeIncl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.requireError cond errorName args)) runtime.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hnextScopeIncl
        simpa using compiledStmtStep_requireError_continue_case
          (spec := spec) (fields := fields) (scope := scope) (runtime := runtime)
          (state := state) (helperFuel := helperFuel) (extraFuel := extraFuel)
          (condVal := condVal) (cond := cond) (errorName := errorName) (args := args)
          (failCond := failCond) (revertStmts := revertStmts)
          hCondSrc hzero hfailEval' hexact' hscope' hbounded hruntime

theorem compiledStmtStep_requireError
    {spec : CompilationModel} {fields : List Field} {scope : List String} {cond : Expr}
    {errorName : String} {args : List Expr} {failCond : YulExpr} {revertStmts : List YulStmt}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hhelperSurface : exprTouchesUnsupportedHelperSurface cond = false)
    (hnextScopeIncl : FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.requireError cond errorName args)) scope)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.requireError cond errorName args) = Except.ok [YulStmt.if_ failCond revertStmts])
    (hrevertExec : ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next) :
    CompiledStmtStepWithHelpers spec fields scope (.requireError cond errorName args)
      [YulStmt.if_ failCond revertStmts] :=
  by
    have _ : exprTouchesUnsupportedHelperSurface cond = false := hhelperSurface
    exact compiledStmtStep_requireError_impl hcore hinScope hnextScopeIncl hfailCompile
      hcompile hrevertExec

theorem compiledStmtStep_revertError
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {errorName : String}
    {args : List Expr}
    {revertStmts : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (.revertError errorName args) = Except.ok revertStmts)
    (hrevertExec :
      ∀ state fuel, ∃ next, execIRStmts fuel state revertStmts = .revert next) :
    CompiledStmtStepWithHelpers spec fields scope (.revertError errorName args) revertStmts where
  compileOk := hcompile
  preserves runtime state helperFuel extraFuel hexact hscope hbounded hruntime hslack := by
    rcases hrevertExec state (revertStmts.length + extraFuel + 1) with ⟨revState, hrev⟩
    have hSrcExec :
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
          (.revertError errorName args) = .revert := by
      simp [SourceSemantics.execStmtWithHelpers, SourceSemantics.typedErrorRevertResult]
    refine ⟨.revert, .revert revState, hSrcExec, hrev, ?_⟩
    simp [stmtStepMatchesIRExec]

end Compiler.Proofs.IRGeneration
