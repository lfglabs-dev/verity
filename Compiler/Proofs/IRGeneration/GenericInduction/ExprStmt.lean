import Compiler.Proofs.IRGeneration.GenericInduction.Scope

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- The conclusion of `CompiledStmtStep.preserves` for one runtime/state pair. -/
private abbrev CompiledStmtStepResult (fields : List Field) (scope : List String) (stmt : Stmt)
    (compiledIR : List YulStmt) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (extraFuel : Nat) : Prop :=
  ∃ sourceResult irExec,
    SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
    execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
    stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- A compiled core expression evaluates to the same bounded word in the source
semantics and in the IR interpreter. -/
private theorem evalIRExpr_eq_evalExpr_of_core
    {fields : List Field} {scope : List String} {value : Expr} {valueIR : YulExpr}
    {runtime : SourceSemantics.RuntimeState} {state : IRState}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    ∃ v, evalIRExpr state valueIR = some v ∧
      SourceSemantics.evalExpr fields runtime value = some v ∧
      v < Compiler.Constants.evmModulus := by
  have hpresent := FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
  have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
    hbounded hpresent hruntime
  have hlt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope
    hbounded hpresent hruntime
  rw [hvalueIR] at heval
  simp [Except.toOption] at heval
  rcases hIR : evalIRExpr state valueIR with _ | v
  · simp [hIR, Option.bind] at heval
  · simp [hIR, Option.bind] at heval
    have hsrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
    rw [hsrc] at hlt
    simp at hlt
    exact ⟨v, rfl, hsrc, hlt⟩

/-- Executing a singleton `let` whose initializer evaluates to `v`. -/
private theorem execIRStmts_let_single
    {state : IRState} {name : String} {valueIR : YulExpr} {v extraFuel : Nat}
    (hIR : evalIRExpr state valueIR = some v) :
    execIRStmts (1 + extraFuel + 1) state [YulStmt.let_ name valueIR] =
      .continue (state.setVar name v) := by
  show (match execIRStmt (1 + extraFuel) state (YulStmt.let_ name valueIR) with
        | .continue s' => execIRStmts (1 + extraFuel) s' []
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) = .continue (state.setVar name v)
  have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
  rw [hfuel_eq]
  simp only [execIRStmt, hIR]
  simp [execIRStmts]

/-- Executing a singleton assignment whose right-hand side evaluates to `v`. -/
private theorem execIRStmts_assign_single
    {state : IRState} {name : String} {valueIR : YulExpr} {v extraFuel : Nat}
    (hIR : evalIRExpr state valueIR = some v) :
    execIRStmts (1 + extraFuel + 1) state [YulStmt.assign name valueIR] =
      .continue (state.setVar name v) := by
  show (match execIRStmt (1 + extraFuel) state (YulStmt.assign name valueIR) with
        | .continue s' => execIRStmts (1 + extraFuel) s' []
        | .return v s => .return v s
        | .stop s => .stop s
        | .revert s => .revert s) = .continue (state.setVar name v)
  have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
  rw [hfuel_eq]
  simp only [execIRStmt, hIR]
  simp [execIRStmts]

/-- Binding `name := v` on both sides re-establishes the step invariants on any
tail scope included in `name :: scope`. -/
private theorem stmtStepMatchesIRExec_continue_bindValue
    {fields : List Field} {scope nextScope : List String}
    {runtime : SourceSemantics.RuntimeState} {state : IRState} {name : String} {v : Nat}
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hlt : v < Compiler.Constants.evmModulus)
    (hincl : FunctionBody.scopeNamesIncluded nextScope (name :: scope)) :
    stmtStepMatchesIRExec fields nextScope
      (.continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v })
      (.continue (state.setVar name v)) := by
  simp only [stmtStepMatchesIRExec]
  exact ⟨FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v,
    FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included
      (FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact) hincl,
    FunctionBody.bindingsBounded_bindValue hbounded name v hlt,
    FunctionBody.scopeNamesPresent_of_included
      (FunctionBody.scopeNamesPresent_cons_bindValue hscope) hincl⟩

private theorem compiledStmtStep_letVar_preserves
    {fields : List Field} {scope : List String} {name : String} {value : Expr}
    {valueIR : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {extraFuel : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    CompiledStmtStepResult fields scope (.letVar name value) [YulStmt.let_ name valueIR]
      runtime state extraFuel := by
  obtain ⟨v, hIR, hsrc, hlt⟩ :=
    evalIRExpr_eq_evalExpr_of_core hcore hinScope hvalueIR hexact hscope hbounded hruntime
  refine ⟨.continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v },
    .continue (state.setVar name v), ?_, execIRStmts_let_single hIR, ?_⟩
  · simp [SourceSemantics.execStmt, hsrc]
  · -- A `letVar` introduces just its bound name into the tail scope.
    refine stmtStepMatchesIRExec_continue_bindValue hexact hscope hbounded hruntime hlt ?_
    intro n hn
    simpa [stmtNextScope, collectStmtBindNames] using hn

theorem compiledStmtStep_letVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.letVar name value) [YulStmt.let_ name valueIR] where
  compileOk := by
    have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
  preserves _ _ _ hexact hscope hbounded hruntime _ :=
    compiledStmtStep_letVar_preserves hcore hinScope hvalueIR hexact hscope hbounded hruntime

private theorem compiledStmtStep_assignVar_preserves
    {fields : List Field} {scope : List String} {name : String} {value : Expr}
    {valueIR : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {extraFuel : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    CompiledStmtStepResult fields scope (.assignVar name value) [YulStmt.assign name valueIR]
      runtime state extraFuel := by
  obtain ⟨v, hIR, hsrc, hlt⟩ :=
    evalIRExpr_eq_evalExpr_of_core hcore hinScope hvalueIR hexact hscope hbounded hruntime
  refine ⟨.continue { runtime with bindings := SourceSemantics.bindValue runtime.bindings name v },
    .continue (state.setVar name v), ?_, execIRStmts_assign_single hIR, ?_⟩
  · simp [SourceSemantics.execStmt, hsrc]
  · refine stmtStepMatchesIRExec_continue_bindValue hexact hscope hbounded hruntime hlt ?_
    intro n hn
    simp [stmtNextScope, collectStmtBindNames] at hn
    exact List.mem_cons_of_mem _ hn

theorem compiledStmtStep_assignVar
    {fields : List Field}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.assignVar name value) [YulStmt.assign name valueIR] where
  compileOk := by
    have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal]
  preserves _ _ _ hexact hscope hbounded hruntime _ :=
    compiledStmtStep_assignVar_preserves hcore hinScope hvalueIR hexact hscope hbounded hruntime

/-- A failing `require` (condition word `0`) reverts on both sides. -/
private theorem compiledStmtStep_require_revert
    {fields : List Field} {scope : List String} {cond : Expr} {message : String}
    {failCond : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {extraFuel : Nat}
    (hfailEval : evalIRExpr state failCond = some 1)
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some 0) :
    CompiledStmtStepResult fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)]
      runtime state extraFuel := by
  rcases FunctionBody.execIRStmts_revertWithMessage_revert
      (fuel := extraFuel) (state := state) message with ⟨revState, hrev⟩
  have hstmt :
      execIRStmt (extraFuel + 1) state
        (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
          .revert revState := by
    simp [execIRStmt, hfailEval, hrev]
  refine ⟨.revert (.raw (Denote.errorStringBytes message)), .revert revState, ?_, ?_,
    by simp [stmtStepMatchesIRExec]⟩
  · simp [SourceSemantics.execStmt, hCondSrc]
  · rw [show [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
        extraFuel + 1 = Nat.succ (extraFuel + 1) by simp; omega]
    simp [execIRStmts, hstmt]

/-- A passing `require` (non-zero condition word) continues with unchanged state. -/
private theorem compiledStmtStep_require_continue
    {fields : List Field} {scope : List String} {cond : Expr} {message : String}
    {failCond : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {extraFuel condVal : Nat}
    (hfailEval : evalIRExpr state failCond = some 0)
    (hCondSrc : SourceSemantics.evalExpr fields runtime cond = some condVal)
    (hzero : ¬condVal = 0)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    CompiledStmtStepResult fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)]
      runtime state extraFuel := by
  -- A `require` introduces no bindings into the tail scope.
  have hNextScopeIncl : FunctionBody.scopeNamesIncluded
      (stmtNextScope scope (.require cond message)) scope := by
    intro n hn
    simpa [stmtNextScope, collectStmtBindNames] using hn
  refine ⟨.continue runtime, .continue state, ?_, ?_, ?_⟩
  · simp [SourceSemantics.execStmt, hCondSrc, hzero]
  · rw [show [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
        extraFuel + 1 = Nat.succ (extraFuel + 1) by simp; omega]
    simp [execIRStmts, execIRStmt, hfailEval]
  · simp only [stmtStepMatchesIRExec]
    exact ⟨hruntime,
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hNextScopeIncl,
      hbounded, FunctionBody.scopeNamesPresent_of_included hscope hNextScopeIncl⟩

private theorem compiledStmtStep_require_preserves
    {fields : List Field} {scope : List String} {cond : Expr} {message : String}
    {failCond : YulExpr} {runtime : SourceSemantics.RuntimeState} {state : IRState}
    {extraFuel : Nat}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hfailCompile :
      CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    CompiledStmtStepResult fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)]
      runtime state extraFuel := by
  rcases FunctionBody.eval_compileRequireFailCond_core_of_scope hcore hexact hinScope hbounded
      (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime with
    ⟨failCond', hfailCompile', hfailEval⟩
  cases hfailCompile.symm.trans hfailCompile'
  rcases FunctionBody.compileExpr_core_ok (fields := fields) hcore with ⟨condIR, hcondIR⟩
  obtain ⟨condVal, -, hCondSrc, -⟩ :=
    evalIRExpr_eq_evalExpr_of_core hcore hinScope hcondIR hexact hscope hbounded hruntime
  by_cases hzero : condVal = 0
  · exact compiledStmtStep_require_revert
      (by simpa [hCondSrc, hzero, SourceSemantics.boolWord] using hfailEval) (hzero ▸ hCondSrc)
  · exact compiledStmtStep_require_continue
      (by simpa [hCondSrc, hzero, SourceSemantics.boolWord] using hfailEval) hCondSrc hzero
      hexact hscope hbounded hruntime

theorem compiledStmtStep_require
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {message : String}
    {failCond : YulExpr}
    (hcore : FunctionBody.ExprCompileCore cond)
    (hinScope : FunctionBody.exprBoundNamesInScope cond scope)
    (hfailCompile : CompilationModel.compileRequireFailCond fields .calldata cond = Except.ok failCond) :
    CompiledStmtStep fields scope (.require cond message)
      [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] where
  compileOk := by
    have hfailCompileInternal := hfailCompile
    rw [← CompilationModel.compileRequireFailCondWithInternals_nil_eq] at hfailCompileInternal
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hfailCompileInternal]
  preserves _ _ _ hexact hscope hbounded hruntime _ :=
    compiledStmtStep_require_preserves hcore hinScope hfailCompile hexact hscope hbounded hruntime

/-- The two-statement `mstore(0, value); return(0, 32)` lowering of `return`. -/
private abbrev compiledReturnIR (valueIR : YulExpr) : List YulStmt :=
  [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
  , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]

private theorem compiledReturnIR_fuel_eq {valueIR : YulExpr} {extraFuel : Nat}
    (hslack : sizeOf (compiledReturnIR valueIR) - (compiledReturnIR valueIR).length ≤ extraFuel) :
    (compiledReturnIR valueIR).length + extraFuel + 1 =
      sizeOf (compiledReturnIR valueIR) +
        (extraFuel - (sizeOf (compiledReturnIR valueIR) - 2)) + 1 := by
  have hlen : 2 ≤ sizeOf (compiledReturnIR valueIR) := by
    show 2 ≤ 1 + sizeOf (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) +
      (1 + sizeOf (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) + 1)
    omega
  simp only [List.length_cons, List.length_nil] at hslack ⊢
  omega

private theorem execStmt_return_of_evalExpr_eq
    {fields : List Field} {runtime : SourceSemantics.RuntimeState} {value : Expr} {v : Nat}
    (hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v) :
    SourceSemantics.execStmt fields runtime (.return value) =
      .return v { runtime with world := runtime.world.writePhysicalMemoryValue 0 v } := by
  have hunfold : SourceSemantics.execStmt fields runtime (.return value) =
    match SourceSemantics.evalExpr fields runtime value with
    | some resolved => .return resolved
        { runtime with world := runtime.world.writePhysicalMemoryValue 0 resolved }
    | none => .revert .empty := rfl
  rw [hunfold, hEvalSrc]

private theorem compiledStmtStep_return_preserves
    {fields : List Field} {scope : List String} {value : Expr} {valueIR : YulExpr}
    {runtime : SourceSemantics.RuntimeState} {state : IRState} {extraFuel : Nat}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR)
    (hexact : FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state)
    (hscope : FunctionBody.scopeNamesPresent scope runtime.bindings)
    (hbounded : FunctionBody.bindingsBounded runtime.bindings)
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hslack : sizeOf (compiledReturnIR valueIR) - (compiledReturnIR valueIR).length ≤ extraFuel) :
    CompiledStmtStepResult fields scope (.return value) (compiledReturnIR valueIR)
      runtime state extraFuel := by
  obtain ⟨v, -, hEvalSrc, -⟩ :=
    evalIRExpr_eq_evalExpr_of_core hcore hinScope hvalueIR hexact hscope hbounded hruntime
  rcases FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope (tailIR := [])
      (extraFuel := extraFuel - (sizeOf (compiledReturnIR valueIR) - 2)) hcore hexact hinScope
      hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime with
    ⟨valueIR', hvalueIR', hwhole⟩
  rw [hvalueIR] at hvalueIR'
  cases hvalueIR'
  refine ⟨_, .return v (state.writePhysicalMemoryValue 0 v),
    execStmt_return_of_evalExpr_eq hEvalSrc, ?_, ?_⟩
  · simp only [List.append_nil, hEvalSrc, Option.getD_some] at hwhole
    rw [compiledReturnIR_fuel_eq hslack]
    exact hwhole
  · simp [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames]
    exact FunctionBody.runtimeStateMatchesIR_writePhysicalMemoryValue hruntime 0 v

theorem compiledStmtStep_return
    {fields : List Field}
    {scope : List String}
    {value : Expr}
    {valueIR : YulExpr}
    (hcore : FunctionBody.ExprCompileCore value)
    (hinScope : FunctionBody.exprBoundNamesInScope value scope)
    (hvalueIR : CompilationModel.compileExpr fields .calldata value = Except.ok valueIR) :
    CompiledStmtStep fields scope (.return value)
      [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ] where
  compileOk := by
    have hvalueIRInternal := hvalueIR
    rw [← CompilationModel.compileExprWithInternals_nil_eq] at hvalueIRInternal
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hvalueIRInternal,
      pure, Except.pure, bind, Except.bind]
  preserves _ _ _ hexact hscope hbounded hruntime hslack :=
    compiledStmtStep_return_preserves hcore hinScope hvalueIR hexact hscope hbounded hruntime
      hslack

theorem compiledStmtStep_stop
    {fields : List Field}
    {scope : List String} :
    CompiledStmtStep fields scope .stop [YulStmt.exprStmt (YulExpr.call "stop" [])] where
  compileOk := by
    simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, pure, Except.pure]
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Use the helper with wholeFuel aligned to the fuel budget
    set compiledIR := [YulStmt.exprStmt (YulExpr.call "stop" [])]
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hwhole := FunctionBody.execIRStmts_compiled_stop_core_append_wholeFuel
      (state := state) (tailIR := []) (extraFuel := wholeExtraFuel)
    simp only [List.append_nil] at hwhole
    -- Show the fuel values match
    have hfuelEq : compiledIR.length + extraFuel + 1 =
        sizeOf compiledIR + wholeExtraFuel + 1 := by
      rw [hWF]
      have : compiledIR.length ≤ sizeOf compiledIR := by
        show 1 ≤ sizeOf compiledIR
        change 1 ≤ sizeOf ([YulStmt.exprStmt (YulExpr.call "stop" [])] : List YulStmt)
        decide
      omega
    refine ⟨.stop runtime, .stop state, ?_, ?_, ?_⟩
    · simp [SourceSemantics.execStmt]
    · rw [hfuelEq]; exact hwhole
    · simpa [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames] using hruntime

end Compiler.Proofs.IRGeneration
