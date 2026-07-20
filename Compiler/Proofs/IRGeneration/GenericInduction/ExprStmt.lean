import Compiler.Proofs.IRGeneration.GenericInduction.Scope

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

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
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- none case: contradiction (eval_compileExpr_core_of_scope guarantees some)
      simp [hIR, Option.bind] at heval
    · -- some v case: both source and IR succeed
      simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      -- Value is bounded
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact
          hinScope hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
      rw [hEvalSrc] at hvalueLt
      simp at hvalueLt
      -- Define the post-states
      set state' := state.setVar name v
      set runtime' := { runtime with
        bindings := SourceSemantics.bindValue runtime.bindings name v }
      -- IR execution: execIRStmts for a singleton [let_ name valueIR]
      -- Fuel = 1 + extraFuel + 1; execIRStmts strips one level, execIRStmt uses extraFuel
      have hIRExec : execIRStmts (1 + extraFuel + 1) state [YulStmt.let_ name valueIR] =
          .continue state' := by
        -- 1 + extraFuel + 1 = (extraFuel + 1) + 1 = Nat.succ (extraFuel + 1)
        -- execIRStmts strips the outer succ: execIRStmt (extraFuel + 1) state (let_ ...)
        -- extraFuel + 1 = Nat.succ extraFuel; execIRStmt unfolds to match on evalIRExpr
        show (match execIRStmt (1 + extraFuel) state (YulStmt.let_ name valueIR) with
              | .continue s' => execIRStmts (1 + extraFuel) s' []
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) = .continue state'
        have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
        rw [hfuel_eq]
        simp only [execIRStmt, hIR, state']
        simp [execIRStmts]
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime (.letVar name value) =
          .continue runtime' := by
        simp [SourceSemantics.execStmt, hEvalSrc, runtime']
      -- Fuel equality
      have hfuelEq : [YulStmt.let_ name valueIR].length + extraFuel + 1 =
          1 + extraFuel + 1 := by simp
      -- Post-state invariants
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v
      have hexact_base : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (name :: scope) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
      -- A `letVar` introduces just its bound name into the tail scope.
      have hNextScopeIncl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.letVar name value)) (name :: scope) := by
        intro n hn
        simpa [stmtNextScope, collectStmtBindNames] using hn
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.letVar name value)) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact_base hNextScopeIncl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
        FunctionBody.bindingsBounded_bindValue hbounded name v hvalueLt
      have hscope_base : FunctionBody.scopeNamesPresent
          (name :: scope) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_cons_bindValue hscope
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.letVar name value)) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope_base hNextScopeIncl
      -- Provide witnesses
      refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
      · exact hSrcExec
      · rw [hfuelEq]; exact hIRExec
      · simp [stmtStepMatchesIRExec]
        exact ⟨hruntime', hexact', hbounded', hscope'⟩

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
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- Case split on evalIRExpr to extract the Nat value
    rcases hIR : evalIRExpr state valueIR with _ | v
    · -- none case: contradiction
      simp [hIR, Option.bind] at heval
    · -- some v case: both source and IR succeed
      simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      -- Value is bounded
      have hvalueLt := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact
          hinScope hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
      rw [hEvalSrc] at hvalueLt
      simp at hvalueLt
      -- Define the post-states
      set state' := state.setVar name v
      set runtime' := { runtime with
        bindings := SourceSemantics.bindValue runtime.bindings name v }
      -- IR execution
      have hIRExec : execIRStmts (1 + extraFuel + 1) state [YulStmt.assign name valueIR] =
          .continue state' := by
        show (match execIRStmt (1 + extraFuel) state (YulStmt.assign name valueIR) with
              | .continue s' => execIRStmts (1 + extraFuel) s' []
              | .return v s => .return v s
              | .stop s => .stop s
              | .revert s => .revert s) = .continue state'
        have hfuel_eq : 1 + extraFuel = Nat.succ extraFuel := by omega
        rw [hfuel_eq]
        simp only [execIRStmt, hIR, state']
        simp [execIRStmts]
      -- Source execution
      have hSrcExec : SourceSemantics.execStmt fields runtime (.assignVar name value) =
          .continue runtime' := by
        simp [SourceSemantics.execStmt, hEvalSrc, runtime']
      -- Fuel equality
      have hfuelEq : [YulStmt.assign name valueIR].length + extraFuel + 1 =
          1 + extraFuel + 1 := by simp
      -- Post-state invariants
      have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' :=
        FunctionBody.runtimeStateMatchesIR_setVar_bindValue hruntime name v
      have hexact_base : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (name :: scope) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hexact
      have hNextScopeIncl : FunctionBody.scopeNamesIncluded
          (stmtNextScope scope (.assignVar name value)) (name :: scope) := by
        intro n hn
        simp [stmtNextScope, collectStmtBindNames] at hn
        exact List.mem_cons_of_mem _ hn
      have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
          (stmtNextScope scope (.assignVar name value)) runtime'.bindings state' :=
        FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact_base hNextScopeIncl
      have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
        FunctionBody.bindingsBounded_bindValue hbounded name v hvalueLt
      have hscope_base : FunctionBody.scopeNamesPresent
          (name :: scope) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_cons_bindValue hscope
      have hscope' : FunctionBody.scopeNamesPresent
          (stmtNextScope scope (.assignVar name value)) runtime'.bindings :=
        FunctionBody.scopeNamesPresent_of_included hscope_base hNextScopeIncl
      -- Provide witnesses
      refine ⟨.continue runtime', .continue state', ?_, ?_, ?_⟩
      · exact hSrcExec
      · rw [hfuelEq]; exact hIRExec
      · simp [stmtStepMatchesIRExec]
        exact ⟨hruntime', hexact', hbounded', hscope'⟩

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
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    have hpresent : FunctionBody.exprBoundNamesPresent cond runtime.bindings :=
      FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope
    -- Get the fail condition evaluation
    rcases FunctionBody.eval_compileRequireFailCond_core_of_scope
        hcore hexact hinScope hbounded hpresent hruntime with
      ⟨failCond', hfailCompile', hfailEval⟩
    rw [hfailCompile] at hfailCompile'
    injection hfailCompile' with hfailEq
    subst hfailEq
    -- Get the source condition evaluation
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
      · -- condVal = 0 → require fails → revert
        have hfailEval' : evalIRExpr state failCond = some 1 := by
          rw [hCondSrc, hzero] at hfailEval
          simpa [SourceSemantics.boolWord] using hfailEval
        -- Execute the if_ statement: failCond = 1 → enters revert block
        rcases FunctionBody.execIRStmts_revertWithMessage_revert
            (fuel := extraFuel) (state := state) message with
          ⟨revState, hrev⟩
        have hstmt :
            execIRStmt (extraFuel + 1) state
              (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                .revert revState := by
          simp [execIRStmt, hfailEval', hrev]
        have hIRExec :
            execIRStmts (1 + extraFuel + 1) state
              [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] =
                .revert revState := by
          have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
          rw [this]; simp [execIRStmts, hstmt]
        have hSrcExec :
            SourceSemantics.execStmt fields runtime (.require cond message) = .revert := by
          simp [SourceSemantics.execStmt, hCondSrc, hzero]
        have hfuelEq :
            [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
              extraFuel + 1 = 1 + extraFuel + 1 := by simp
        refine ⟨.revert, .revert revState, hSrcExec, ?_, ?_⟩
        · rw [hfuelEq]; exact hIRExec
        · simp [stmtStepMatchesIRExec]
      · -- condVal ≠ 0 → require passes → continue
        have hfailEval' : evalIRExpr state failCond = some 0 := by
          have : SourceSemantics.evalExpr fields runtime cond ≠ some 0 := by
            rw [hCondSrc]; simp [hzero]
          simpa [this, SourceSemantics.boolWord] using hfailEval
        have hstmt' :
            execIRStmt (extraFuel + 1) state
              (YulStmt.if_ failCond (CompilationModel.revertWithMessage message)) =
                .continue state := by
          simp [execIRStmt, hfailEval']
        have hIRExec :
            execIRStmts (1 + extraFuel + 1) state
              [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)] =
                .continue state := by
          have : 1 + extraFuel + 1 = Nat.succ (extraFuel + 1) := by omega
          rw [this]; simp [execIRStmts, hstmt']
        have hSrcExec :
            SourceSemantics.execStmt fields runtime (.require cond message) =
              .continue runtime := by
          simp [SourceSemantics.execStmt, hCondSrc, hzero]
        have hfuelEq :
            [YulStmt.if_ failCond (CompilationModel.revertWithMessage message)].length +
              extraFuel + 1 = 1 + extraFuel + 1 := by simp
        -- A `require` introduces no bindings into the tail scope.
        have hNextScopeIncl : FunctionBody.scopeNamesIncluded
            (stmtNextScope scope (.require cond message)) scope := by
          intro n hn
          simpa [stmtNextScope, collectStmtBindNames] using hn
        have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
            (stmtNextScope scope (.require cond message)) runtime.bindings state :=
          FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexact hNextScopeIncl
        have hscope' : FunctionBody.scopeNamesPresent
            (stmtNextScope scope (.require cond message)) runtime.bindings :=
          FunctionBody.scopeNamesPresent_of_included hscope hNextScopeIncl
        refine ⟨.continue runtime, .continue state, hSrcExec, ?_, ?_⟩
        · rw [hfuelEq]; exact hIRExec
        · simp [stmtStepMatchesIRExec]
          exact ⟨hruntime, hexact', hbounded, hscope'⟩

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
  preserves runtime state extraFuel hexact hscope hbounded hruntime hslack := by
    set compiledIR :=
      [ YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])
      , YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32]) ]
    set wholeExtraFuel := extraFuel - (sizeOf compiledIR - compiledIR.length) with hWF
    have hwhole := FunctionBody.execIRStmts_compiled_return_core_append_wholeFuel_of_scope
        (fields := fields) (runtime := runtime) (state := state) (scope := scope)
        (value := value) (tailIR := []) (extraFuel := wholeExtraFuel)
        hcore hexact hinScope hbounded
        (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    simp only [List.append_nil] at hwhole
    rcases hwhole with ⟨valueIR', hvalueIR', hwhole⟩
    rw [hvalueIR] at hvalueIR'
    injection hvalueIR' with hEq
    subst hEq
    -- Establish that evalExpr succeeds (returns some) via the compile-eval theorem
    have heval := FunctionBody.eval_compileExpr_core_of_scope hcore hexact hinScope
        hbounded (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
    rw [hvalueIR] at heval
    simp [Except.toOption] at heval
    -- heval now relates evalIRExpr to evalExpr; extract that evalExpr = some v
    rcases hIR : evalIRExpr state valueIR with _ | v
    · simp [hIR, Option.bind] at heval
    · simp [hIR, Option.bind] at heval
      have hEvalSrc : SourceSemantics.evalExpr fields runtime value = some v := heval.symm
      have hRetVal : (SourceSemantics.evalExpr fields runtime value).getD 0 = v := by
        rw [hEvalSrc]; rfl
      -- Fuel equality
      have hfuelEq : compiledIR.length + extraFuel + 1 =
          sizeOf compiledIR + wholeExtraFuel + 1 := by
        rw [hWF]
        have : compiledIR.length ≤ sizeOf compiledIR := by
          show 2 ≤ sizeOf compiledIR
          have : 0 ≤ sizeOf (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) :=
            Nat.zero_le _
          have : 0 ≤ sizeOf (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) :=
            Nat.zero_le _
          show 2 ≤ 1 + sizeOf (YulStmt.exprStmt (YulExpr.call "mstore" [YulExpr.lit 0, valueIR])) +
                       (1 + sizeOf (YulStmt.exprStmt (YulExpr.call "return" [YulExpr.lit 0, YulExpr.lit 32])) + 1)
          omega
        omega
      -- Provide explicit witnesses
      set state' := { state with memory := fun o => if o = 0 then v else state.memory o }
      have hlt : v < Verity.Core.Uint256.modulus := by
        have := FunctionBody.evalExpr_lt_evmModulus_core_of_scope hcore hexact hinScope hbounded
          (FunctionBody.exprBoundNamesPresent_of_scope hscope hinScope) hruntime
        rw [hEvalSrc] at this; exact this
      set runtime' : SourceSemantics.RuntimeState :=
        { runtime with world := { runtime.world with
            memory := fun o => if o = 0 then v else runtime.world.memory o } }
      refine ⟨.return v runtime', .return v state', ?_, ?_, ?_⟩
      · show SourceSemantics.execStmt fields runtime (.return value) = .return v runtime'
        have hunfold : SourceSemantics.execStmt fields runtime (.return value) =
          match SourceSemantics.evalExpr fields runtime value with
          | some resolved => .return resolved
              { runtime with world := { runtime.world with
                  memory := fun o => if o = 0 then resolved else runtime.world.memory o } }
          | none => .revert := rfl
        rw [hunfold, hEvalSrc]
      · rw [hRetVal] at hwhole; rw [hfuelEq]; exact hwhole
      · simp [stmtStepMatchesIRExec, stmtNextScope, collectStmtNames]
        exact FunctionBody.runtimeStateMatchesIR_setBothMemory hruntime 0 v hlt

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
