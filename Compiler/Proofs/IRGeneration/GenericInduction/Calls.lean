import Compiler.Proofs.IRGeneration.GenericInduction.Core

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- A one-statement lowering whose source↔IR bridge is stated at `irFuel + 3`
discharges the helper-aware step interface: the singleton's size forces
`1 ≤ extraFuel`, so the bridge is instantiated at `extraFuel - 1`. -/
private theorem compiledStmtStepWithHelpersAndHelperIR_singleton
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {stmt : Stmt} {irStmt : YulStmt}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false
      scope [] stmt = Except.ok [irStmt])
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields (stmtNextScope scope stmt)
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt)
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state [irStmt])) :
    CompiledStmtStepWithHelpersAndHelperIR runtimeContract spec fields scope stmt [irStmt] where
  compileOk := hcompile
  preserves runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack := by
    have hfuel : [irStmt].length + extraFuel + 1 = (extraFuel - 1) + 3 := by
      simp at hslack ⊢
      omega
    rw [hfuel]
    exact ⟨_, _, rfl, rfl,
      bridge runtime state helperFuel _ hfuelPos hexact hscope hbounded hruntime⟩

private theorem compiledIR_eq_of_compileStmt_internalCallAssign
    {spec : CompilationModel} {fields : List Field} {scope names : List String}
    {calleeName : String} {args : List Expr} {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false
      scope [] (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs) :
    compiledIR = [YulStmt.letMany names
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] := by
  have hcompileEmpty : CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] using hcompile
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCallAssign_shape hcompileEmpty
  cases hargCompile.symm.trans hargOk
  exact hshape

private theorem compiledIR_eq_of_compileStmt_internalCall
    {spec : CompilationModel} {fields : List Field} {scope : List String}
    {calleeName : String} {args : List Expr} {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false
      scope [] (Stmt.internalCall calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs) :
    compiledIR = [YulStmt.exprStmt
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] := by
  have hcompileEmpty : CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      (Stmt.internalCall calleeName args) = Except.ok compiledIR := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] using hcompile
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape hcompileEmpty
  cases hargCompile.symm.trans hargOk
  exact hshape

/-- Constructor for the helper-aware single-step interface when the head
statement is `Stmt.internalCallAssign`. The proof is parameterised by a single
source-to-IR alignment bridge that the rank-decreasing callee induction will
supply. The bridge captures the end-to-end obligation: given matching
preconditions, the source and IR execution results for this statement match
through `stmtStepMatchesIRExecWithInternals`.

The bridge is quantified over an extra `irFuel` so that the proof can
instantiate it at the right fuel level derived from `extraFuel`.

The `compileOk` obligation is passed through from the compilation hypothesis. -/
theorem compiledStmtStepWithHelpersAndHelperIR_internalCallAssign
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    -- End-to-end source↔IR alignment bridge.
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel : Nat)
        (irFuel : Nat), 0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])) :
    CompiledStmtStepWithHelpersAndHelperIR runtimeContract spec fields scope
      (Stmt.internalCallAssign names calleeName args) compiledIR := by
  obtain rfl := compiledIR_eq_of_compileStmt_internalCallAssign hcompile hargCompile
  exact compiledStmtStepWithHelpersAndHelperIR_singleton hcompile bridge

theorem compiledStmtStepWithHelpersAndHelperIR_internalCall
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCall calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    -- End-to-end source↔IR alignment bridge.
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel : Nat)
        (irFuel : Nat), 0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.exprStmt (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])) :
    CompiledStmtStepWithHelpersAndHelperIR runtimeContract spec fields scope
      (Stmt.internalCall calleeName args) compiledIR := by
  obtain rfl := compiledIR_eq_of_compileStmt_internalCall hcompile hargCompile
  exact compiledStmtStepWithHelpersAndHelperIR_singleton hcompile bridge

theorem compileStmt_internalCallAssign_shape_with_internals
    {fields : List CompilationModel.Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {internalFunctions : List FunctionSpec}
    {names : List String}
    {functionName : String}
    {args : List CompilationModel.Expr}
    {compiledIR : List YulStmt}
    (hok :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (CompilationModel.Stmt.internalCallAssign names functionName args) internalFunctions =
          Except.ok compiledIR) :
    ∃ argExprs,
      CompilationModel.compileInternalCallArgs fields .calldata internalFunctions
          functionName args = Except.ok argExprs ∧
      compiledIR = [YulStmt.letMany names
        (YulExpr.call (CompilationModel.internalFunctionYulName functionName) argExprs)] := by
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hok
  match hargs :
      CompilationModel.compileInternalCallArgs fields .calldata internalFunctions
        functionName args with
  | .error e =>
      simp [hargs] at hok
  | .ok argExprs =>
      refine ⟨argExprs, rfl, ?_⟩
      simp [hargs, pure, Except.pure] at hok
      exact hok.symm

theorem compileStmt_internalCall_shape_with_internals
    {fields : List CompilationModel.Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {internalFunctions : List FunctionSpec}
    {functionName : String}
    {args : List CompilationModel.Expr}
    {compiledIR : List YulStmt}
    (hok :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (CompilationModel.Stmt.internalCall functionName args) internalFunctions =
          Except.ok compiledIR) :
    ∃ argExprs,
      CompilationModel.compileInternalCallArgs fields .calldata internalFunctions
          functionName args = Except.ok argExprs ∧
      compiledIR = [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName functionName) argExprs)] := by
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hok
  match hargs :
      CompilationModel.compileInternalCallArgs fields .calldata internalFunctions
        functionName args with
  | .error e =>
      simp [hargs] at hok
  | .ok argExprs =>
      refine ⟨argExprs, rfl, ?_⟩
      simp [hargs, pure, Except.pure] at hok
      exact hok.symm

/-- Spec-functions-aware constructor for the helper-aware single-step interface
when the head statement is `Stmt.internalCallAssign`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState)
        (helperFuel irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)]))
    (irFuelSlack : Nat := 0) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope
        (Stmt.internalCallAssign names calleeName args) compiledIR irFuelSlack := by
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCallAssign_shape_with_internals hcompile
  have hArgEq : argExprs' = argExprs := by simpa [hargCompile] using hargOk.symm
  subst hArgEq
  set singletonIR := [YulStmt.letMany names
    (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs')]
  have hshape' : compiledIR = singletonIR := by simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by simp [singletonIR]
    rw [hshape'] at hslack; rw [hlenOne] at hslack; omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]; omega
  rw [hshape'] at hslack ⊢; rw [hlenOne] at hslack; rw [hFuelEq]
  exact ⟨_, _, rfl, rfl, hMatch⟩

private theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_delimiter :
    (0 : Nat) = 0 := by
  rfl

abbrev InternalCallAssignWithInternalsBridgeAt
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (helperFuel irFuel : Nat) : Prop :=
    0 < helperFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (Stmt.internalCallAssign names calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.letMany names
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)])

abbrev InternalCallAssignWithInternalsBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) : Prop :=
  ∀ runtime state helperFuel irFuel,
    InternalCallAssignWithInternalsBridgeAt runtimeContract spec fields scope names calleeName
      args argExprs runtime state helperFuel irFuel

abbrev InternalCallAssignWithInternalsSufficientBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    1 < helperFuel →
    helperBodySize + 2 ≤ irFuel →
    InternalCallAssignWithInternalsBridgeAt runtimeContract spec fields scope names calleeName
      args argExprs runtime state helperFuel irFuel

/-- Compositional sufficient-fuel obligation for a direct assignment helper
call.  The helper consumes `helperBodySize + 2` units before recursive
preservation is invoked, so the caller must reserve the downstream slack
additively rather than proving two unrelated upper bounds. -/
abbrev InternalCallAssignWithInternalsAdditiveBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize irFuelSlack : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    1 < helperFuel →
    helperBodySize + 2 + irFuelSlack ≤ irFuel →
    InternalCallAssignWithInternalsBridgeAt runtimeContract spec fields scope names calleeName
      args argExprs runtime state helperFuel irFuel

abbrev InternalCallAssignWithInternalsResidualBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    (¬ 1 < helperFuel ∨ ¬ helperBodySize + 2 ≤ irFuel) →
    InternalCallAssignWithInternalsBridgeAt runtimeContract spec fields scope names calleeName
      args argExprs runtime state helperFuel irFuel

abbrev InternalCallAssignWithInternalsAdditiveResidualBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (names : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize irFuelSlack : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    (¬ 1 < helperFuel ∨ ¬ helperBodySize + 2 + irFuelSlack ≤ irFuel) →
    InternalCallAssignWithInternalsBridgeAt runtimeContract spec fields scope names calleeName
      args argExprs runtime state helperFuel irFuel

/-- Fuel-split variant of the direct assignment-call singleton constructor.

This preserves the existing all-positive-fuel public target while exposing the
two proof obligations that arise in the direct helper-summary path: the normal
sufficient-fuel region and the residual source-low-fuel or IR-insufficient-fuel
region. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_fuelSplitBridge
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (irFuelSlack : Nat := 0)
    (helperBodySize : Nat)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (bridgeSufficient :
      InternalCallAssignWithInternalsAdditiveBridge runtimeContract spec fields scope names
        calleeName args argExprs helperBodySize irFuelSlack)
    (bridgeResidual :
      InternalCallAssignWithInternalsAdditiveResidualBridge runtimeContract spec fields scope names
        calleeName args argExprs helperBodySize irFuelSlack) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope
      (Stmt.internalCallAssign names calleeName args) compiledIR irFuelSlack := by
  refine
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (names := names) (calleeName := calleeName) (args := args)
      (compiledIR := compiledIR) (argExprs := argExprs) hcompile hargCompile ?_ irFuelSlack
  intro runtime state helperFuel irFuel hfuel hexact hscope hbounded hruntime
  by_cases hsource : 1 < helperFuel
  · by_cases hir : helperBodySize + 2 + irFuelSlack ≤ irFuel
    · exact bridgeSufficient runtime state helperFuel irFuel hsource hir
        hfuel hexact hscope hbounded hruntime
    · exact bridgeResidual runtime state helperFuel irFuel (.inr hir)
        hfuel hexact hscope hbounded hruntime
  · exact bridgeResidual runtime state helperFuel irFuel (.inl hsource)
      hfuel hexact hscope hbounded hruntime

/-- Spec-functions-aware constructor for the helper-aware single-step interface
when the head statement is `Stmt.internalCall`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState)
        (helperFuel irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.exprStmt (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)]))
    (irFuelSlack : Nat := 0) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope (Stmt.internalCall calleeName args) compiledIR irFuelSlack := by
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape_with_internals hcompile
  have hArgEq : argExprs' = argExprs := by simpa [hargCompile] using hargOk.symm
  subst hArgEq
  set singletonIR := [YulStmt.exprStmt
    (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs')]
  have hshape' : compiledIR = singletonIR := by simpa [singletonIR] using hshape
  have hlenOne : singletonIR.length = 1 := by simp [singletonIR]
  have hExtraPos : 1 ≤ extraFuel := by
    have hsz : sizeOf singletonIR ≥ 2 := by simp [singletonIR]
    rw [hshape'] at hslack; rw [hlenOne] at hslack; omega
  set irFuel := extraFuel - 1 with hirFuel
  have hMatch := bridge runtime state helperFuel irFuel hfuelPos hexact hscope hbounded hruntime
  have hFuelEq : singletonIR.length + extraFuel + 1 = irFuel + 3 := by
    rw [hlenOne, hirFuel]; omega
  rw [hshape'] at hslack ⊢; rw [hlenOne] at hslack; rw [hFuelEq]
  exact ⟨_, _, rfl, rfl, hMatch⟩

private theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_delimiter :
    (0 : Nat) = 0 := by
  rfl

abbrev InternalCallWithInternalsBridgeAt
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (helperFuel irFuel : Nat) : Prop :=
    0 < helperFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCall calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
        (Stmt.internalCall calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.exprStmt
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)])

abbrev InternalCallWithInternalsBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) : Prop :=
  ∀ runtime state helperFuel irFuel,
    InternalCallWithInternalsBridgeAt runtimeContract spec fields scope calleeName args argExprs
      runtime state helperFuel irFuel

abbrev InternalCallWithInternalsSufficientBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    1 < helperFuel →
    helperBodySize + 2 ≤ irFuel →
    InternalCallWithInternalsBridgeAt runtimeContract spec fields scope calleeName args argExprs
      runtime state helperFuel irFuel

/-- Compositional sufficient-fuel obligation for a direct void helper call.
After entering and executing the helper body, `irFuelSlack` remains available
to the recursive preservation proof.  In particular, equal independent bounds
on the body cost, slack, and caller fuel are intentionally not accepted. -/
abbrev InternalCallWithInternalsAdditiveBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize irFuelSlack : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    1 < helperFuel →
    helperBodySize + 2 + irFuelSlack ≤ irFuel →
    InternalCallWithInternalsBridgeAt runtimeContract spec fields scope calleeName args argExprs
      runtime state helperFuel irFuel

/-- The arithmetic fact needed at the recursive helper boundary: the additive
caller obligation leaves the complete promised slack after subtracting the
helper-entry/body cost. -/
theorem internalCall_irFuelSlack_le_residual
    (helperBodySize irFuelSlack irFuel : Nat)
    (h : helperBodySize + 2 + irFuelSlack ≤ irFuel) :
    irFuelSlack ≤ irFuel - (helperBodySize + 2) := by
  omega

abbrev InternalCallWithInternalsResidualBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    (¬ 1 < helperFuel ∨ ¬ helperBodySize + 2 ≤ irFuel) →
    InternalCallWithInternalsBridgeAt runtimeContract spec fields scope calleeName args argExprs
      runtime state helperFuel irFuel

abbrev InternalCallWithInternalsAdditiveResidualBridge
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (argExprs : List YulExpr) (helperBodySize irFuelSlack : Nat) : Prop :=
  ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState) (helperFuel irFuel : Nat),
    (¬ 1 < helperFuel ∨ ¬ helperBodySize + 2 + irFuelSlack ≤ irFuel) →
    InternalCallWithInternalsBridgeAt runtimeContract spec fields scope calleeName args argExprs
      runtime state helperFuel irFuel

/-- Fuel-split variant of the direct void-call singleton constructor.

The existing public single-step interface still asks for every positive source
helper fuel and every compiled-side wrapper fuel.  This constructor makes the
proof-interface review explicit: callers may discharge the normal
sufficient-fuel region separately from the residual low/insufficient-fuel
region, while preserving the same final `CompiledStmtStep...` target. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_fuelSplitBridge
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (irFuelSlack : Nat := 0)
    (helperBodySize : Nat)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (bridgeSufficient :
      InternalCallWithInternalsAdditiveBridge runtimeContract spec fields scope calleeName args
        argExprs helperBodySize irFuelSlack)
    (bridgeResidual :
      InternalCallWithInternalsAdditiveResidualBridge runtimeContract spec fields scope calleeName args
        argExprs helperBodySize irFuelSlack) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope (Stmt.internalCall calleeName args) compiledIR irFuelSlack := by
  refine
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (args := args)
      (compiledIR := compiledIR) (argExprs := argExprs) hcompile hargCompile ?_ irFuelSlack
  intro runtime state helperFuel irFuel hfuel hexact hscope hbounded hruntime
  by_cases hsource : 1 < helperFuel
  · by_cases hir : helperBodySize + 2 + irFuelSlack ≤ irFuel
    · exact bridgeSufficient runtime state helperFuel irFuel hsource hir
        hfuel hexact hscope hbounded hruntime
    · exact bridgeResidual runtime state helperFuel irFuel (.inr hir)
        hfuel hexact hscope hbounded hruntime
  · exact bridgeResidual runtime state helperFuel irFuel (.inl hsource)
      hfuel hexact hscope hbounded hruntime

/-- Non-vacuous list-level constructor for a direct helper-return-binding head.
This packages `compiledStmtStepWithHelpersAndHelperIR_internalCallAssign` into
the split direct-helper step interface expected by the exact helper-aware list
induction seam. -/
theorem stmtListDirectInternalHelperAssignStepInterface_cons_internalCallAssign
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope
        (Stmt.internalCallAssign names calleeName args)
        compiledIR)
    (hrest :
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        rest) :
    StmtListDirectInternalHelperAssignStepInterface
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCallAssign names calleeName args :: rest) := by
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Non-vacuous `WithInternals` list-level constructor for a direct
helper-return-binding head. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_cons_internalCallAssign
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (irFuelSlack : Nat := 0)
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope
        (Stmt.internalCallAssign names calleeName args)
        compiledIR irFuelSlack)
    (hrest :
      StmtListDirectInternalHelperAssignStepInterfaceWithInternals
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        rest irFuelSlack) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCallAssign names calleeName args :: rest) irFuelSlack := by
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Exact Tier 4 head-step proof object for a function body's direct internal
helper surface. Future helper-rank induction should construct this single
catalog once, then reuse the mechanical list-interface assembly theorems
downstream. -/
structure DirectInternalHelperHeadStepCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCall calleeName args)
          compiledIR
  assign :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCallAssign names calleeName args)
          compiledIR

/-- A statement occurrence together with the scope obtained by processing the
preceding statements in the same list. -/
inductive StmtOccursAtScope :
    List String → List String → Stmt → List Stmt → Prop where
  | head {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      StmtOccursAtScope scope scope stmt (stmt :: rest)
  | tail {scope occurrenceScope : List String} {head target : Stmt} {rest : List Stmt} :
      StmtOccursAtScope (stmtNextScope scope head) occurrenceScope target rest →
      StmtOccursAtScope scope occurrenceScope target (head :: rest)

/-- Spec-functions-aware call-only sibling of
`DirectInternalHelperHeadStepCatalog`.

Direct internal-call heads compile their arguments through
`compileInternalCallArgs ... spec.functions`, so their compiled IR is not
determined by the default empty internal-function compiler argument recorded by
`DirectInternalHelperHeadStepCatalog`. This catalog therefore carries the
`CompiledStmtStepWithHelpersAndHelperIRWithInternals` witnesses directly for
the exact void-call statements at their prefix-derived scopes. Indexing by the
scoped occurrence avoids demanding witnesses for wrong-arity argument lists or
scopes that do not occur in the body. -/
structure DirectInternalHelperCallHeadStepCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (initialScope : List String)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      StmtOccursAtScope initialScope scope (Stmt.internalCall calleeName args) fn.body →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIRWithInternals
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCall calleeName args)
          compiledIR

/-- Spec-functions-aware return-binding-call-only sibling of
`DirectInternalHelperHeadStepCatalog`.

Direct internal-call-assignment heads compile their arguments through
`compileInternalCallArgs ... spec.functions`, so their compiled IR is not
determined by the default empty internal-function compiler argument recorded by
`DirectInternalHelperHeadStepCatalog`. This catalog therefore carries the
`CompiledStmtStepWithHelpersAndHelperIRWithInternals` witnesses directly for
the exact return-binding call statements at their prefix-derived scopes.
Indexing by the scoped occurrence avoids demanding witnesses for wrong-arity
argument lists or scopes that do not occur in the body. -/
structure DirectInternalHelperAssignHeadStepCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (initialScope : List String)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {scope : List String} {names : List String} {calleeName : String}
        {args : List Expr},
      StmtOccursAtScope initialScope scope
        (Stmt.internalCallAssign names calleeName args) fn.body →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIRWithInternals
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCallAssign names calleeName args)
          compiledIR

/-- Body-local head-step catalog for direct `Expr.internalCall` results bound
by `Stmt.letVar`, indexed by their prefix-derived scopes. -/
structure DirectInternalHelperExprCallHeadStepCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (initialScope : List String)
    (fn : FunctionSpec) : Prop where
  exprCall :
    ∀ {scope : List String} {name calleeName : String} {args : List Expr},
      StmtOccursAtScope initialScope scope
        (Stmt.letVar name (Expr.internalCall calleeName args)) fn.body →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIRWithInternals
          runtimeContract spec fields scope
          (Stmt.letVar name (Expr.internalCall calleeName args)) compiledIR

/-- Mid-level Tier 4 seam: future rank induction can package direct-helper
singletons here by proving compilation succeeds for the head and that the exact
singleton IR execution matches the source helper-aware step. The mechanical
`CompiledStmtStepWithHelpersAndHelperIR` construction into
`DirectInternalHelperHeadStepCatalog` is then shared. -/
structure DirectInternalHelperCallHeadStepBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope []
          (Stmt.internalCall calleeName args) = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCall calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.exprStmt (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

structure DirectInternalHelperAssignHeadStepBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {names : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope []
          (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {names : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

/-- Spec-functions-aware direct call bridge. This is the direct-call counterpart
of `DirectInternalHelperCallHeadStepBridge`, but it records the exact
`compileStmt ... spec.functions` shape and the corresponding
`compileInternalCallArgs ... spec.functions` argument compilation. -/
structure DirectInternalHelperCallHeadStepBridgeWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR →
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.exprStmt (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

/-- Spec-functions-aware direct helper-return binding bridge. -/
structure DirectInternalHelperAssignHeadStepBridgeWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String) : Prop where
  compile :
    ∀ {scope : List String} {names : List String} {args : List Expr},
      ∃ compiledIR,
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {names : List String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR →
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

structure DirectInternalHelperHeadStepBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  callCompile :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope []
          (Stmt.internalCall calleeName args) = Except.ok compiledIR
  callBridge :
    ∀ {scope : List String} {calleeName : String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      calleeName ∈ helperCallNames fn →
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCall calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCall calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCall calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.exprStmt (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])
  assignCompile :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope []
          (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR
  assignBridge :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
        {compiledIR : List YulStmt} {argExprs : List YulExpr},
      calleeName ∈ helperCallNames fn →
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (irFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.internalCallAssign names calleeName args))
          (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
            [YulStmt.letMany names (YulExpr.call
              (CompilationModel.internalFunctionYulName calleeName) argExprs)])

/-- Callee-local Tier 4 bridge inventory. This matches
`SupportedBodyHelperInterface.calleeRanksDecrease` directly: future rank
induction can construct one reusable bridge object per referenced helper callee,
and the body-level head-step bridge catalog is assembled mechanically. -/
structure DirectInternalHelperPerCalleeBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName

/-- Call-only half of the callee-local Tier 4 bridge inventory. This lets
void-helper-call consumers avoid requiring unrelated return-binding bridges. -/
structure DirectInternalHelperPerCalleeCallBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName

/-- Project the void-call half of a complete per-callee bridge inventory. This
lets call-only consumers use an already established full bridge catalog without
introducing an assign-bridge obligation at their API boundary. -/
theorem directInternalHelperPerCalleeCallBridgeCatalog_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperPerCalleeCallBridgeCatalog runtimeContract spec fields fn := by
  exact ⟨hbridge.call⟩

/-- Assign-only half of the callee-local Tier 4 bridge inventory. This isolates
the roadmap's current blocker, namely helper-return-binding steps, while the
void-call half remains mechanically vacuous under the current fragment. -/
structure DirectInternalHelperPerCalleeAssignBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName

/-- Project the helper-return-binding half of a complete per-callee bridge
inventory. This lets assign-only consumers use an already established full
bridge catalog without exposing an unrelated void-call obligation. -/
theorem directInternalHelperPerCalleeAssignBridgeCatalog_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn := by
  exact ⟨hbridge.assign⟩

/-- Reassemble the full callee-local bridge catalog from the current supported
body witness plus the assign-only bridge half. The call half is vacuous because
`SupportedStmtList` still excludes direct helper calls from the fragment. -/
theorem directInternalHelperPerCalleeBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn := by
  refine ⟨?_, ?_⟩
  · intro calleeName hmem
    exfalso
    simp [hbody.helperCallNames_nil] at hmem
  · intro calleeName hmem
    exact hassign.assign hmem

/-- Split compile-side Tier 4 inventory. This isolates the purely compilation
obligations from the semantic bridge obligations so future fragment widening can
discharge compile success generically once direct helper calls are admitted into
the supported statement witness. -/
structure DirectInternalHelperPerCalleeCallCompileCatalog
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope []
            (Stmt.internalCall calleeName args) = Except.ok compiledIR

/-- Assign-only half of the compile-side Tier 4 inventory. This isolates the
current fragment-widening blocker once direct helper return-binding calls are
admitted into the supported statement witness. -/
structure DirectInternalHelperPerCalleeAssignCompileCatalog
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      ∀ {scope : List String} {names : List String} {args : List Expr},
        ∃ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope []
            (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR

/-- Reassemble the full compile-side Tier 4 inventory from independently
constructed call and assign halves. -/
theorem directInternalHelperPerCalleeCallCompileCatalog_of_supportedBody
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn) :
    DirectInternalHelperPerCalleeCallCompileCatalog spec fields fn := by
  refine ⟨?_⟩
  intro calleeName hmem
  exfalso
  simp [hbody.helperCallNames_nil] at hmem

theorem directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcallee : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro scope calleeName args hmem
    exact (hcallee.call hmem).compile (scope := scope) (args := args)
  · intro scope calleeName args compiledIR argExprs hmem hcompile hargCompile
    exact (hcallee.call hmem).bridge
      (scope := scope)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile
  · intro scope names calleeName args hmem
    exact (hcallee.assign hmem).compile (scope := scope) (names := names) (args := args)
  · intro scope names calleeName args compiledIR argExprs hmem hcompile hargCompile
    exact (hcallee.assign hmem).bridge
      (scope := scope)
      (names := names)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
      hargCompile

/-- Assemble the body-level direct-helper bridge catalog directly from the
current helper-free supported-body witness plus the assign-only per-callee
bridge inventory. This keeps downstream theorems on the exact assign-only Tier 4
boundary instead of routing through the vacuous per-callee void-call layer. -/
theorem directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn := by
  exact
    directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperPerCalleeBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hbody
        hassign)

private theorem directInternalHelperHeadStepCatalog_call_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    ∀ {scope : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCall calleeName args)
          compiledIR := by
  intro scope calleeName args hmem
  rcases hbridge.callCompile (scope := scope) (calleeName := calleeName)
      (args := args) hmem with ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCall_shape hcompile
  have hcompileSpec : CompilationModel.compileStmt fields spec.events spec.errors
      .calldata [] false scope [] (Stmt.internalCall calleeName args) =
        Except.ok compiledIR := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] using hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIR_internalCall
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (calleeName := calleeName)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompileSpec
      hargCompile
      (hbridge.callBridge
        (scope := scope)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hmem
        hcompile
        hargCompile)

private theorem directInternalHelperHeadStepCatalog_assign_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
      calleeName ∈ helperCallNames fn →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract
          spec
          fields
          scope
          (Stmt.internalCallAssign names calleeName args)
          compiledIR := by
  intro scope names calleeName args hmem
  rcases hbridge.assignCompile (scope := scope) (names := names) (calleeName := calleeName) (args := args) hmem with
    ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCallAssign_shape hcompile
  have hcompileSpec :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork] using hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIR_internalCallAssign
      hcompileSpec
      hargCompile
      (hbridge.assignBridge
        (scope := scope)
        (names := names)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hmem
        hcompile
        hargCompile)

/-- Build the reusable direct-helper head-step catalog from the lighter bridge
catalog seam. This keeps future helper-rank induction focused on exact singleton
bridges instead of reconstructing `CompiledStmtStepWithHelpersAndHelperIR`
objects by hand at every theorem layer. -/
theorem directInternalHelperHeadStepCatalog_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbridge : DirectInternalHelperHeadStepBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
  refine ⟨?_, ?_⟩
  · exact directInternalHelperHeadStepCatalog_call_of_bridgeCatalog hbridge
  · exact directInternalHelperHeadStepCatalog_assign_of_bridgeCatalog hbridge

/-- Assemble the reusable direct-helper head-step catalog directly from the more
rank-induction-friendly per-callee bridge inventory. This lets downstream
wrapper theorems consume the exact catalog object future rank induction should
build, without routing through the intermediate body-level bridge catalog. -/
theorem directInternalHelperHeadStepCatalog_of_perCalleeBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hcallee : DirectInternalHelperPerCalleeBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
  exact
    directInternalHelperHeadStepCatalog_of_bridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperHeadStepBridgeCatalog_of_perCalleeBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hcallee)

/-- Assemble the exact body-level direct-helper head-step catalog directly from
the split compile/semantic Tier 4 inventories. This removes the last per-callee
bridge detour once callers already provide the compile catalog and semantic
bridge data separately. -/
theorem directInternalHelperHeadStepCatalog_of_supportedBody_and_assignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {fn : FunctionSpec}
    (hbody : SupportedBodyInterface spec fn)
    (hassign :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn := by
  exact
    directInternalHelperHeadStepCatalog_of_bridgeCatalog
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (fn := fn)
      (directInternalHelperHeadStepBridgeCatalog_of_supportedBody_and_assignBridgeCatalog
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (fn := fn)
        hbody
        hassign)

private theorem eraseDups_nodup_and_mem_aux_local [BEq α] [LawfulBEq α]
    (n : Nat) (l : List α) (hlen : l.length ≤ n) :
    (l.eraseDups).Nodup ∧ (∀ a, a ∈ l.eraseDups ↔ a ∈ l) := by
  induction n generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
      subst this
      exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
  | succ n ih =>
      match l with
      | [] => exact ⟨List.Pairwise.nil, fun _ => Iff.rfl⟩
      | x :: xs =>
          rw [List.eraseDups_cons]
          have hfilt_len : (xs.filter fun b => !b == x).length ≤ n := by
            have := List.length_filter_le (fun b => !b == x) xs
            simp [List.length_cons] at hlen
            omega
          have ⟨ihNd, ihMem⟩ := ih _ hfilt_len
          constructor
          · rw [List.nodup_cons]
            constructor
            · intro h
              have hmf := (ihMem x).mp h
              rw [List.mem_filter] at hmf
              have := hmf.2
              simp at this
            · exact ihNd
          · intro a
            constructor
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · exact Or.inr (List.mem_filter.mp ((ihMem a).mp h)).1
            · intro h
              rw [List.mem_cons] at h ⊢
              rcases h with rfl | h
              · exact Or.inl rfl
              · by_cases heq : a == x
                · exact Or.inl (beq_iff_eq.mp heq)
                · exact Or.inr ((ihMem a).mpr (List.mem_filter.mpr ⟨h, by simp [heq]⟩))

private theorem List.mem_eraseDups_iff_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} : a ∈ l.eraseDups ↔ a ∈ l :=
  (eraseDups_nodup_and_mem_aux_local l.length l (Nat.le_refl _)).2 a

private theorem List.mem_eraseDups_of_mem_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l) : a ∈ l.eraseDups :=
  List.mem_eraseDups_iff_local.mpr h

private theorem List.mem_of_mem_eraseDups_local [BEq α] [LawfulBEq α]
    {a : α} {l : List α} (h : a ∈ l.eraseDups) : a ∈ l :=
  List.mem_eraseDups_iff_local.mp h

private theorem internalCallAssign_callee_mem_stmtListInternalHelperCallNames_eraseDups
    {names : List String} {calleeName : String} {args : List Expr} {rest : List Stmt} :
    calleeName ∈
      (stmtListInternalHelperCallNames
        (Stmt.internalCallAssign names calleeName args :: rest)).eraseDups := by
  apply List.mem_eraseDups_of_mem_local
  simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]

private theorem internalCall_callee_mem_stmtListInternalHelperCallNames_eraseDups
    {calleeName : String} {args : List Expr} {rest : List Stmt} :
    calleeName ∈
      (stmtListInternalHelperCallNames
        (Stmt.internalCall calleeName args :: rest)).eraseDups := by
  apply List.mem_eraseDups_of_mem_local
  simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]

private theorem mem_stmtListInternalHelperCallNames_cons_of_mem_tail
    {stmt : Stmt} {rest : List Stmt} {calleeName : String}
    (hrest : calleeName ∈ stmtListInternalHelperCallNames rest) :
    calleeName ∈ stmtListInternalHelperCallNames (stmt :: rest) := by
  simp [stmtListInternalHelperCallNames, hrest]

/-- Assemble the exact direct-helper-assign list interface from a reusable
single-head constructor. This pushes future helper-rank induction down to the
only genuinely new work: constructing the `Stmt.internalCallAssign` head step
itself. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCallAssign names calleeName args =>
          rcases hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect

/-- Assemble the exact `WithInternals` direct-helper-assign list interface from
a reusable single-head constructor. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_internalCallAssignSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIRWithInternals
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCallAssign names calleeName args =>
          rcases hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect

/-- Assemble the exact direct-helper-assign list interface from head-step
constructors indexed only by helper callees that actually occur in the current
statement list. This is the precise seam future helper-rank induction should
target: it no longer needs to quantify over arbitrary helper names unrelated to
the body under proof. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCallAssign names calleeName args =>
            rcases hstep
                (scope := scope)
                (names := names)
                (calleeName := calleeName)
                (args := args)
                internalCallAssign_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect
      · apply ih
        intro scope names calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

/-- Assemble the exact `WithInternals` direct-helper-assign list interface from
head-step constructors indexed only by helper callees in the current list. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_internalCallAssignSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {names : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIRWithInternals
            runtimeContract spec fields scope
            (Stmt.internalCallAssign names calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCallAssign names calleeName args =>
            rcases hstep
                (scope := scope)
                (names := names)
                (calleeName := calleeName)
                (args := args)
                internalCallAssign_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect
      · apply ih
        intro scope names calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (names := names) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

/-- Non-vacuous list-level constructor for a direct helper statement head.
This packages `compiledStmtStepWithHelpersAndHelperIR_internalCall` into the
split direct-helper call interface expected by the exact helper-aware list
induction seam. -/
theorem stmtListDirectInternalHelperCallStepInterface_cons_internalCall
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope
        (Stmt.internalCall calleeName args)
        compiledIR)
    (hrest :
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        rest) :
    StmtListDirectInternalHelperCallStepInterface
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCall calleeName args :: rest) := by
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Non-vacuous `WithInternals` list-level constructor for a direct helper
statement head. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_cons_internalCall
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (irFuelSlack : Nat := 0)
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope
        (Stmt.internalCall calleeName args)
        compiledIR irFuelSlack)
    (hrest :
      StmtListDirectInternalHelperCallStepInterfaceWithInternals
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        rest irFuelSlack) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCall calleeName args :: rest) irFuelSlack := by
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Assemble the exact direct-helper-call list interface from a reusable
single-head constructor. This is the theorem future helper-rank induction
should target: once it can build `CompiledStmtStepWithHelpersAndHelperIR` for
an arbitrary `Stmt.internalCall` head, the surrounding list recursion is
mechanical. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCall calleeName args =>
          rcases hstep (scope := scope) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect

/-- Assemble the exact `WithInternals` direct-helper-call list interface from a
reusable single-head constructor. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_internalCallSteps
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIRWithInternals
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ih
      intro hdirect
      cases stmt with
      | internalCall calleeName args =>
          rcases hstep (scope := scope) (calleeName := calleeName) (args := args) with
            ⟨compiledIR, hcompiled⟩
          exact ⟨compiledIR, hcompiled⟩
      | _ =>
          simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect

/-- Assemble the exact direct-helper-call list interface from head-step
constructors indexed only by helper callees that actually occur in the current
statement list. This matches the `helperCallNames`-based rank inventory carried
by `SupportedBodyHelperInterface`, avoiding arbitrary-name quantification at the
function theorem boundary. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCall calleeName args =>
            rcases hstep
                (scope := scope)
                (calleeName := calleeName)
                (args := args)
                internalCall_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect
      · apply ih
        intro scope calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

/-- Assemble the exact `WithInternals` direct-helper-call list interface from
head-step constructors indexed only by helper callees in the current list. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_internalCallSteps_of_helperCallNames
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {calleeName : String} {args : List Expr},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIRWithInternals
            runtimeContract spec fields scope
            (Stmt.internalCall calleeName args)
            compiledIR) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hdirect
        cases stmt with
        | internalCall calleeName args =>
            rcases hstep
                (scope := scope)
                (calleeName := calleeName)
                (args := args)
                internalCall_callee_mem_stmtListInternalHelperCallNames_eraseDups with
              ⟨compiledIR, hcompiled⟩
            exact ⟨compiledIR, hcompiled⟩
        | _ =>
            simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect
      · apply ih
        intro scope calleeName args hmem
        have hrest : calleeName ∈ stmtListInternalHelperCallNames rest :=
          List.mem_of_mem_eraseDups_local hmem
        exact hstep (scope := scope) (calleeName := calleeName) (args := args)
          (List.mem_eraseDups_of_mem_local
            (mem_stmtListInternalHelperCallNames_cons_of_mem_tail hrest))

/-- Assemble both exact direct-helper list interfaces from a single body-local
head-step catalog. This keeps the list recursion mechanical so future
rank-decreasing helper proofs can focus on constructing one catalog object. -/
theorem stmtListDirectInternalHelperStepInterfaces_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec} :
    DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn →
    StmtListDirectInternalHelperCallStepInterface
      runtimeContract
      spec
      fields
      scope
      fn.body ∧
    StmtListDirectInternalHelperAssignStepInterface
      runtimeContract
      spec
      fields
      scope
      fn.body := by
  intro hcatalog
  constructor
  · exact
      stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := fn.body)
        hcatalog.call
  · exact
      stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := fn.body)
        hcatalog.assign

/-- Assemble the exact direct void-helper-call list interface from a body-local
head-step catalog.  Unlike
`stmtListDirectInternalHelperStepInterfaces_of_headStepCatalog`, this consumer
does not expose or require the return-binding interface: the call proof is
obtained solely from the catalog's void-call execution witnesses. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperHeadStepCatalog runtimeContract spec fields fn) :
    StmtListDirectInternalHelperCallStepInterface
      runtimeContract spec fields scope fn.body := by
  exact
    stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := fn.body)
      hcatalog.call

/-- Assemble the exact spec-functions-aware direct void-helper-call list
interface from a body-local call-only `WithInternals` head-step catalog. This is the
`WithInternals` counterpart of
`stmtListDirectInternalHelperCallStepInterface_of_headStepCatalog`: it records
the `compileStmt ... spec.functions` head shape that direct internal calls
actually compile through. The recursion retains each call's prefix-derived
scope, so the catalog is only queried for call sites at scopes that occur in the
body. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperCallHeadStepCatalogWithInternals
        runtimeContract spec fields scope fn) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract spec fields scope fn.body := by
  have go :
      ∀ {currentScope : List String} {stmts : List Stmt},
        (∀ {occurrenceScope : List String} {stmt : Stmt},
          StmtOccursAtScope currentScope occurrenceScope stmt stmts →
          StmtOccursAtScope scope occurrenceScope stmt fn.body) →
        StmtListDirectInternalHelperCallStepInterfaceWithInternals
          runtimeContract spec fields currentScope stmts := by
    intro currentScope stmts hembed
    induction stmts generalizing currentScope with
    | nil =>
        exact .nil
    | cons stmt rest ih =>
        refine .cons ?_ ?_
        · intro hdirect
          cases stmt with
          | internalCall calleeName args =>
              rcases hcatalog.call
                  (scope := currentScope) (calleeName := calleeName) (args := args)
                  (hembed StmtOccursAtScope.head) with
                ⟨compiledIR, hcompiled⟩
              exact ⟨compiledIR, hcompiled⟩
          | _ =>
              simp [stmtTouchesDirectInternalHelperCallSurface] at hdirect
        · apply ih
          intro occurrenceScope tailStmt hocc
          exact hembed (StmtOccursAtScope.tail hocc)
  exact go (fun hocc => hocc)

/-- Assemble the exact spec-functions-aware direct return-binding-helper-call
list interface from a body-local assign-only `WithInternals` head-step catalog.
This is the `WithInternals` counterpart of the assign half of
`stmtListDirectInternalHelperStepInterfaces_of_headStepCatalog`: it records the
`compileStmt ... spec.functions` head shape that direct internal call
assignments actually compile through. The recursion retains each call's
prefix-derived scope, so the catalog is only queried for call sites at scopes
that occur in the body. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperAssignHeadStepCatalogWithInternals
        runtimeContract spec fields scope fn) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract spec fields scope fn.body := by
  have go :
      ∀ {currentScope : List String} {stmts : List Stmt},
        (∀ {occurrenceScope : List String} {stmt : Stmt},
          StmtOccursAtScope currentScope occurrenceScope stmt stmts →
          StmtOccursAtScope scope occurrenceScope stmt fn.body) →
        StmtListDirectInternalHelperAssignStepInterfaceWithInternals
          runtimeContract spec fields currentScope stmts := by
    intro currentScope stmts hembed
    induction stmts generalizing currentScope with
    | nil =>
        exact .nil
    | cons stmt rest ih =>
        refine .cons ?_ ?_
        · intro hdirect
          cases stmt with
          | internalCallAssign names calleeName args =>
              rcases hcatalog.assign
                  (scope := currentScope) (names := names)
                  (calleeName := calleeName) (args := args)
                  (hembed StmtOccursAtScope.head) with
                ⟨compiledIR, hcompiled⟩
              exact ⟨compiledIR, hcompiled⟩
          | _ =>
              simp [stmtTouchesDirectInternalHelperAssignSurface] at hdirect
        · apply ih
          intro occurrenceScope tailStmt hocc
          exact hembed (StmtOccursAtScope.tail hocc)
  exact go (fun hocc => hocc)

/-- Assemble the consumed spec-functions-aware expression-helper list interface
for bodies whose expression-helper surface consists exactly of direct
`Expr.internalCall` results bound by `Stmt.letVar`. The coverage premise keeps
the catalog narrow while making the resulting witness directly usable as the
`hexpr` input of `fullHelperAwareListWitnessWithInternals_of_allInterfaces`. -/
theorem stmtListDirectInternalHelperExprCallStepInterfaceWithInternals_of_headStepCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperExprCallHeadStepCatalogWithInternals
        runtimeContract spec fields scope fn)
    (hcoverage :
      ∀ {occurrenceScope : List String} {stmt : Stmt},
        StmtOccursAtScope scope occurrenceScope stmt fn.body →
        stmtTouchesExprInternalHelperSurface stmt = true →
        ∃ name calleeName args,
          stmt = Stmt.letVar name (Expr.internalCall calleeName args)) :
    StmtListExprInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope fn.body := by
  have go :
      ∀ {currentScope : List String} {stmts : List Stmt},
        (∀ {occurrenceScope : List String} {stmt : Stmt},
          StmtOccursAtScope currentScope occurrenceScope stmt stmts →
          StmtOccursAtScope scope occurrenceScope stmt fn.body) →
        StmtListExprInternalHelperStepInterfaceWithInternals
          runtimeContract spec fields currentScope stmts := by
    intro currentScope stmts hembed
    induction stmts generalizing currentScope with
    | nil =>
        exact .nil
    | cons stmt rest ih =>
        refine .cons ?_ ?_
        · intro hexpr
          rcases hcoverage (hembed StmtOccursAtScope.head) hexpr with
            ⟨name, calleeName, args, rfl⟩
          exact hcatalog.exprCall (hembed StmtOccursAtScope.head)
        · apply ih
          intro occurrenceScope tailStmt hocc
          exact hembed (StmtOccursAtScope.tail hocc)
  exact go (fun hocc => hocc)

private theorem internalFunctionYulName_head (calleeName : String) :
    (CompilationModel.internalFunctionYulName calleeName).toList.head? = some 'i' := by
  simp [CompilationModel.internalFunctionYulName, CompilationModel.internalFunctionPrefix]
  left
  decide

private theorem internalFunctionYulName_ne_of_head
    (calleeName builtin : String) (c : Char)
    (hbuiltin : builtin.toList.head? = some c) (hne : 'i' ≠ c) :
    CompilationModel.internalFunctionYulName calleeName ≠ builtin := by
  intro hEq
  have hHead := congrArg (fun s => s.toList.head?) hEq
  change (CompilationModel.internalFunctionYulName calleeName).toList.head? =
    builtin.toList.head? at hHead
  rw [internalFunctionYulName_head calleeName, hbuiltin] at hHead
  exact hne (Option.some.inj hHead)

private theorem internalFunctionYulName_ne_stop
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "stop" := by
  exact internalFunctionYulName_ne_of_head calleeName "stop" 's' (by decide) (by decide)

private theorem internalFunctionYulName_ne_selfdestruct
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "selfdestruct" := by
  exact internalFunctionYulName_ne_of_head calleeName "selfdestruct" 's'
    (by decide) (by decide)

private theorem internalFunctionYulName_ne_invalid
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "invalid" := by
  intro hEq
  have hLen := congrArg String.length hEq
  have hMe : (CompilationModel.internalFunctionYulName calleeName).length =
      9 + calleeName.length := by
    show (toString "internal_" ++ toString calleeName).length =
      9 + calleeName.length
    rw [String.length_append]
    simp [toString]
    decide
  rw [hMe] at hLen
  have h7 : ("invalid" : String).length = 7 := by decide
  omega

private theorem internalFunctionYulName_ne_sstore
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "sstore" := by
  exact internalFunctionYulName_ne_of_head calleeName "sstore" 's' (by decide) (by decide)

private theorem internalFunctionYulName_ne_mstore
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "mstore" := by
  exact internalFunctionYulName_ne_of_head calleeName "mstore" 'm' (by decide) (by decide)

private theorem internalFunctionYulName_ne_returndatacopy
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "returndatacopy" := by
  exact internalFunctionYulName_ne_of_head calleeName "returndatacopy" 'r'
    (by decide) (by decide)

private theorem internalFunctionYulName_ne_revert
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "revert" := by
  exact internalFunctionYulName_ne_of_head calleeName "revert" 'r' (by decide) (by decide)

private theorem internalFunctionYulName_ne_return
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "return" := by
  exact internalFunctionYulName_ne_of_head calleeName "return" 'r' (by decide) (by decide)

private theorem internalFunctionYulName_ne_tstore
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "tstore" := by
  exact internalFunctionYulName_ne_of_head calleeName "tstore" 't' (by decide) (by decide)

private theorem internalFunctionYulName_ne_calldatacopy
    (calleeName : String) :
    CompilationModel.internalFunctionYulName calleeName ≠ "calldatacopy" := by
  exact internalFunctionYulName_ne_of_head calleeName "calldatacopy" 'c'
    (by decide) (by decide)

/-- The compiled-helper witness pins a runtime helper under the callee's Yul name. -/
private theorem exists_findInternalFunction?_of_compiledHelperWitness
    {spec : CompilationModel} {runtimeContract : IRContract} {calleeName : String}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName) :
    ∃ helper, findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper := by
  have hfindSome :
      (findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName)).isSome = true := by
    simpa [compiledHelper.sourceWitness.nameEq] using
      (findInternalFunction?_of_compileInternalFunction_mem
        compiledHelper.compileOk compiledHelper.presentInRuntime)
  exact Option.isSome_iff_exists.mp hfindSome

/-- A singleton void call to an internal helper dispatches to the helper body:
helper Yul names never collide with the builtins the interpreter special-cases. -/
private theorem execIRStmtsWithInternals_singleton_internalFunctionYulName_call
    {contract : IRContract} {fuel : Nat} {state state' : IRState} {calleeName : String}
    {args : List YulExpr} {helper : IRInternalFunctionDef} {argVals : List Nat}
    (hargs : evalIRExprsWithInternals contract (fuel + 1) state args = .values argVals state')
    (hfind : findInternalFunction? contract
      (CompilationModel.internalFunctionYulName calleeName) = some helper) :
    execIRStmtsWithInternals contract (fuel + 3) state
      [YulStmt.exprStmt (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) args)] =
      match execIRInternalFunctionWithInternals contract fuel state' helper argVals with
      | .values _ state'' => .continue state''
      | .stop state'' => .stop state''
      | .return value' state'' => .return value' state''
      | .revert state'' => .revert state'' :=
  execIRStmtsWithInternals_singleton_expr_call_internal contract fuel state _ args helper argVals
    state' hargs hfind (internalFunctionYulName_ne_stop calleeName)
    (internalFunctionYulName_ne_sstore calleeName) (internalFunctionYulName_ne_mstore calleeName)
    (internalFunctionYulName_ne_tstore calleeName)
    (internalFunctionYulName_ne_calldatacopy calleeName)
    (internalFunctionYulName_ne_returndatacopy calleeName)
    (internalFunctionYulName_ne_revert calleeName) (internalFunctionYulName_ne_return calleeName)
    (internalFunctionYulName_ne_invalid calleeName)
    (internalFunctionYulName_ne_selfdestruct calleeName)
    (internalFunctionYulName_isYulLogName_false calleeName)

private theorem execIRStmtsWithInternals_letMany_of_compile
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    {state state' : IRState} {irFuel : Nat} {argVals : List Nat}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.letMany names
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values values state'' =>
            if names.length = values.length then .continue (state''.setVars (names.zip values))
            else .revert state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  obtain ⟨argExprs', hargOk, rfl⟩ := compileStmt_internalCallAssign_shape hcompile
  cases hargCompile.symm.trans hargOk
  obtain ⟨helper, hfind⟩ := exists_findInternalFunction?_of_compiledHelperWitness compiledHelper
  exact ⟨helper, rfl, hfind, execIRStmtsWithInternals_singleton_letMany_call_internal
    runtimeContract irFuel state names _ argExprs helper argVals state' hargs hfind⟩

private theorem execIRStmtsWithInternals_internalCall_of_shape
    {runtimeContract : IRContract} {spec : CompilationModel} {calleeName : String}
    {compiledIR : List YulStmt} {argExprs : List YulExpr}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    {state state' : IRState} {irFuel : Nat} {argVals : List Nat}
    (hshape : compiledIR = [YulStmt.exprStmt
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)])
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values _ state'' => .continue state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  obtain ⟨helper, hfind⟩ := exists_findInternalFunction?_of_compiledHelperWitness compiledHelper
  subst hshape
  exact ⟨helper, rfl, hfind,
    execIRStmtsWithInternals_singleton_internalFunctionYulName_call hargs hfind⟩

/-- Runtime-helper-table packaged version of
`execIRStmtsWithInternals_of_internalCallAssign_compile`: the caller no longer
threads a raw `findInternalFunction?` hypothesis by hand, only the compiled
helper witness coming from `SupportedRuntimeHelperTableInterface`. -/
theorem execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState) (irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.letMany names
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values values state'' =>
            if names.length = values.length then .continue (state''.setVars (names.zip values))
            else .revert state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  exact execIRStmtsWithInternals_letMany_of_compile compiledHelper hcompile hargCompile hargs

/-- Runtime-helper-table packaged version of
`execIRStmtsWithInternals_of_internalCall_compile`: the caller no longer threads
raw helper lookup or builtin-name side conditions by hand. -/
theorem execIRStmtsWithInternals_of_internalCall_compiledHelperWitness
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr} {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState) (irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (hcompile : CompilationModel.compileStmt fields [] [] .calldata [] false scope []
      (Stmt.internalCall calleeName args) = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile : CompilationModel.compileExprList fields .calldata args = Except.ok argExprs)
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values _ state'' => .continue state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape hcompile
  cases hargCompile.symm.trans hargOk
  exact execIRStmtsWithInternals_internalCall_of_shape compiledHelper hshape hargs

/-- Runtime-helper-table packaged dispatch for a direct helper return-binding
compiled with the caller's internal-function environment. -/
theorem execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness_with_internals
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState) (irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile : CompilationModel.compileInternalCallArgs fields .calldata spec.functions
      calleeName args = Except.ok argExprs)
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.letMany names
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values values state'' =>
            if names.length = values.length then .continue (state''.setVars (names.zip values))
            else .revert state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  obtain ⟨argExprs', hargOk, hshape⟩ :=
    compileStmt_internalCallAssign_shape_with_internals hcompile
  have hArgEq : argExprs' = argExprs := by
    simp [hargCompile] at hargOk
    exact hargOk.symm
  subst argExprs'
  obtain ⟨retNames, bodyStmts, hfind, hcompiled⟩ :=
    findInternalFunction?_exact_of_compileInternalFunction_mem_unique
      compiledHelper.compileOk compiledHelper.presentInRuntime (by
        simpa [compiledHelper.sourceWitness.nameEq] using compiledHelper.uniqueInRuntime)
  refine ⟨{ name := CompilationModel.internalFunctionYulName calleeName
            params := CompilationModel.internalFunctionYulParamNames compiledHelper.sourceWitness.callee.params
            rets := retNames
            body := bodyStmts }, hshape, ?_, ?_⟩
  · simpa [compiledHelper.sourceWitness.nameEq] using hfind
  · rw [hshape]
    exact execIRStmtsWithInternals_singleton_letMany_call_internal runtimeContract irFuel state
      names (CompilationModel.internalFunctionYulName calleeName) argExprs _ argVals state'
      hargs (by simpa [compiledHelper.sourceWitness.nameEq] using hfind)

/-- Runtime-helper-table packaged dispatch for a direct void helper call
compiled with the caller's internal-function environment. -/
theorem execIRStmtsWithInternals_of_internalCall_compiledHelperWitness_with_internals
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr} {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState) (irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile : CompilationModel.compileInternalCallArgs fields .calldata spec.functions
      calleeName args = Except.ok argExprs)
    (hargs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    ∃ helper, compiledIR = [YulStmt.exprStmt
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
        match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
        | .values _ state'' => .continue state''
        | .stop state'' => .stop state''
        | .return value' state'' => .return value' state''
        | .revert state'' => .revert state'' := by
  obtain ⟨argExprs', hargOk, hshape⟩ := compileStmt_internalCall_shape_with_internals hcompile
  cases hargCompile.symm.trans hargOk
  exact execIRStmtsWithInternals_internalCall_of_shape compiledHelper hshape hargs

/-- Package a `DirectInternalHelperCallHeadStepBridgeWithInternals` witness into
the exact `CompiledStmtStepWithHelpersAndHelperIRWithInternals` head-step
interface at any scope and argument list. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_of_callBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperCallHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope (Stmt.internalCall calleeName args) compiledIR := by
  rcases hbridge.compile (scope := scope) (args := args) with ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCall_shape_with_internals hcompile
  exact ⟨compiledIR,
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall
      hcompile hargCompile (hbridge.bridge hcompile hargCompile)⟩

/-- Package a `DirectInternalHelperAssignHeadStepBridgeWithInternals` witness
into the exact `CompiledStmtStepWithHelpersAndHelperIRWithInternals` head-step
interface at any scope, return-binding list, and argument list. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_of_assignBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperAssignHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope
        (Stmt.internalCallAssign names calleeName args) compiledIR := by
  rcases hbridge.compile (scope := scope) (names := names) (args := args) with
    ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ :=
    compileStmt_internalCallAssign_shape_with_internals hcompile
  exact ⟨compiledIR,
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign
      hcompile hargCompile (hbridge.bridge hcompile hargCompile)⟩

theorem calleeName_mem_stmtListInternalHelperCallNames_of_stmtOccursAtScope_internalCall
    {initialScope scope : List String}
    {calleeName : String}
    {args : List Expr}
    {stmts : List Stmt}
    (hocc : StmtOccursAtScope initialScope scope (Stmt.internalCall calleeName args) stmts) :
    calleeName ∈ stmtListInternalHelperCallNames stmts := by
  induction stmts generalizing initialScope scope with
  | nil =>
      cases hocc
  | cons head rest ih =>
      cases hocc with
      | head =>
          simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
      | tail htail =>
          exact mem_stmtListInternalHelperCallNames_cons_of_mem_tail (ih htail)

theorem calleeName_mem_helperCallNames_of_stmtOccursAtScope_internalCall
    {initialScope scope : List String}
    {calleeName : String}
    {args : List Expr}
    {fn : FunctionSpec}
    (hocc : StmtOccursAtScope initialScope scope (Stmt.internalCall calleeName args) fn.body) :
    calleeName ∈ helperCallNames fn := by
  exact List.mem_eraseDups_of_mem_local
    (calleeName_mem_stmtListInternalHelperCallNames_of_stmtOccursAtScope_internalCall hocc)

theorem calleeName_mem_stmtListInternalHelperCallNames_of_stmtOccursAtScope_internalCallAssign
    {initialScope scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {stmts : List Stmt}
    (hocc :
      StmtOccursAtScope initialScope scope
        (Stmt.internalCallAssign names calleeName args) stmts) :
    calleeName ∈ stmtListInternalHelperCallNames stmts := by
  induction stmts generalizing initialScope scope with
  | nil =>
      cases hocc
  | cons head rest ih =>
      cases hocc with
      | head =>
          simp [stmtListInternalHelperCallNames, stmtInternalHelperCallNames]
      | tail htail =>
          exact mem_stmtListInternalHelperCallNames_cons_of_mem_tail (ih htail)

theorem calleeName_mem_helperCallNames_of_stmtOccursAtScope_internalCallAssign
    {initialScope scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {fn : FunctionSpec}
    (hocc :
      StmtOccursAtScope initialScope scope
        (Stmt.internalCallAssign names calleeName args) fn.body) :
    calleeName ∈ helperCallNames fn := by
  exact List.mem_eraseDups_of_mem_local
    (calleeName_mem_stmtListInternalHelperCallNames_of_stmtOccursAtScope_internalCallAssign hocc)

/-- Spec-functions-aware per-callee call-only bridge catalog for `fn`. -/
structure DirectInternalHelperPerCalleeCallBridgeCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperCallHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName

/-- Spec-functions-aware per-callee return-binding bridge catalog for `fn`. -/
structure DirectInternalHelperPerCalleeAssignBridgeCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName

/-- Complete spec-functions-aware per-callee bridge catalog for `fn`. -/
structure DirectInternalHelperPerCalleeBridgeCatalogWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (fn : FunctionSpec) : Prop where
  call :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperCallHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName
  assign :
    ∀ {calleeName : String},
      calleeName ∈ helperCallNames fn →
      DirectInternalHelperAssignHeadStepBridgeWithInternals
        runtimeContract spec fields calleeName

theorem directInternalHelperCallHeadStepCatalogWithInternals_of_perCalleeCallBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {initialScope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperPerCalleeCallBridgeCatalogWithInternals
        runtimeContract spec fields fn) :
    DirectInternalHelperCallHeadStepCatalogWithInternals
      runtimeContract spec fields initialScope fn := by
  refine ⟨?_⟩
  intro scope calleeName args hocc
  exact compiledStmtStepWithHelpersAndHelperIRWithInternals_of_callBridge
    (hcatalog.call (calleeName_mem_helperCallNames_of_stmtOccursAtScope_internalCall hocc))

theorem directInternalHelperAssignHeadStepCatalogWithInternals_of_perCalleeAssignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {initialScope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperPerCalleeAssignBridgeCatalogWithInternals
        runtimeContract spec fields fn) :
    DirectInternalHelperAssignHeadStepCatalogWithInternals
      runtimeContract spec fields initialScope fn := by
  refine ⟨?_⟩
  intro scope names calleeName args hocc
  exact compiledStmtStepWithHelpersAndHelperIRWithInternals_of_assignBridge
    (hcatalog.assign
      (calleeName_mem_helperCallNames_of_stmtOccursAtScope_internalCallAssign hocc))

theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_perCalleeCallBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperPerCalleeCallBridgeCatalogWithInternals
        runtimeContract spec fields fn) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract spec fields scope fn.body := by
  exact
    stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_headStepCatalog
      (directInternalHelperCallHeadStepCatalogWithInternals_of_perCalleeCallBridgeCatalog
        hcatalog)

theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_perCalleeAssignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hcatalog :
      DirectInternalHelperPerCalleeAssignBridgeCatalogWithInternals
        runtimeContract spec fields fn) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract spec fields scope fn.body := by
  exact
    stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_headStepCatalog
      (directInternalHelperAssignHeadStepCatalogWithInternals_of_perCalleeAssignBridgeCatalog
        hcatalog)

abbrev InternalCallHelperBodyAlign
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope : List String) (calleeName : String) (args : List Expr)
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (runtime : SourceSemantics.RuntimeState) (state' : IRState)
    (fuel irFuel : Nat) (argVals : List Nat) : Prop :=
  ∀ helper,
    findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper →
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCall calleeName args))
      (let hresult := SourceSemantics.interpretInternalFunctionFuel spec fuel
          compiledHelper.sourceWitness.callee runtime.world argVals
       if hresult.success then
         .continue { runtime with world := hresult.world }
       else
         .revert hresult.revertPayload)
      (match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
       | .values _ state'' => .continue state''
       | .stop state'' => .stop state''
       | .return value' state'' => .return value' state''
       | .revert state'' => .revert state'')

/-- Source-to-IR dispatch reduction for `Stmt.internalCall` when the callee is backed
by a `SupportedCompiledInternalHelperWitness`. Combines the source helper-witness
dispatch (`SourceSemantics.execStmtWithHelpers_internalCall_of_witness`) with the
runtime-helper-table IR dispatch
(`execIRStmtsWithInternals_of_internalCall_compiledHelperWitness_with_internals`). -/
theorem stmtStepMatchesIRExecWithInternals_internalCall_of_compiledHelperWitness
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {calleeName : String} {args : List Expr} {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (fuel irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR)
    (argExprs : List YulExpr)
    (hargCompile : CompilationModel.compileInternalCallArgs fields .calldata spec.functions
      calleeName args = Except.ok argExprs)
    (hsrcArgs : SourceSemantics.evalExprListWithHelpers spec fields (fuel + 1) runtime args =
      some argVals)
    (hirArgs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state')
    (hbodyAlign :
      InternalCallHelperBodyAlign runtimeContract spec fields scope calleeName args
        compiledHelper runtime state' fuel irFuel argVals) :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCall calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields (fuel + 1) runtime
        (Stmt.internalCall calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.exprStmt
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  obtain ⟨helper, hshape, hfind, hirExec⟩ :=
    execIRStmtsWithInternals_of_internalCall_compiledHelperWitness_with_internals
      compiledHelper state irFuel hcompile argExprs hargCompile hirArgs
  rw [hshape] at hirExec
  rw [SourceSemantics.execStmtWithHelpers_internalCall_of_witness
    compiledHelper.sourceWitness hnodup, hsrcArgs, hirExec]
  simpa using hbodyAlign helper hfind

abbrev InternalCallAssignHelperBodyAlign
    (runtimeContract : IRContract) (spec : CompilationModel) (fields : List Field)
    (scope names : List String) (calleeName : String) (args : List Expr)
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (runtime : SourceSemantics.RuntimeState) (state' : IRState)
    (fuel irFuel : Nat) (argVals : List Nat) : Prop :=
  ∀ helper,
    findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper →
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
      (let hresult := SourceSemantics.interpretInternalFunctionFuel spec fuel
          compiledHelper.sourceWitness.callee runtime.world argVals
       if hresult.success then
         match names, hresult.returnValue with
         | [name], some value =>
             .continue { runtime with
               world := hresult.world
               bindings := SourceSemantics.bindValue runtime.bindings name value
             }
         | _, _ => .revert .empty
       else
         .revert hresult.revertPayload)
      (match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
       | .values values state'' =>
           if names.length = values.length then
             .continue (state''.setVars (names.zip values))
           else .revert state''
       | .stop state'' => .stop state''
       | .return value' state'' => .return value' state''
       | .revert state'' => .revert state'')

/-- Source-to-IR dispatch reduction for `Stmt.internalCallAssign` when the callee is
backed by a `SupportedCompiledInternalHelperWitness`. Combines
`SourceSemantics.execStmtWithHelpers_internalCallAssign_of_witness` with
`execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness_with_internals`. -/
theorem stmtStepMatchesIRExecWithInternals_internalCallAssign_of_compiledHelperWitness
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {names : List String} {calleeName : String} {args : List Expr}
    {compiledIR : List YulStmt}
    (compiledHelper : SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (fuel irFuel : Nat) {argVals : List Nat} {state' : IRState}
    (argExprs : List YulExpr)
    (hbodyAlign :
      InternalCallAssignHelperBodyAlign runtimeContract spec fields scope names calleeName args
        compiledHelper runtime state' fuel irFuel argVals)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (hcompile : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile : CompilationModel.compileInternalCallArgs fields .calldata spec.functions
      calleeName args = Except.ok argExprs)
    (hsrcArgs : SourceSemantics.evalExprListWithHelpers spec fields (fuel + 1) runtime args =
      some argVals)
    (hirArgs : evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
      .values argVals state') :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields (fuel + 1) runtime
        (Stmt.internalCallAssign names calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.letMany names
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  obtain ⟨helper, hshape, hfind, hirExec⟩ :=
    execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness_with_internals
      compiledHelper state irFuel hcompile argExprs hargCompile hirArgs
  rw [hshape] at hirExec
  rw [SourceSemantics.execStmtWithHelpers_internalCallAssign_of_witness
    compiledHelper.sourceWitness hnodup, hsrcArgs, hirExec]
  have halign := hbodyAlign helper hfind
  rcases names with _ | ⟨name, _ | ⟨_, _⟩⟩ <;>
    cases hret :
      (SourceSemantics.interpretInternalFunctionFuel spec fuel
        compiledHelper.sourceWitness.callee runtime.world argVals).returnValue <;>
    simpa [hret] using halign

/-! ## External Call Module (`Stmt.ecm`) Layer 2 Step Interface (`F4`) -/

/-- `Stmt.ecm` compilation depends only on `fields`, `dynamicSource`, and
`internalFunctions`; it is definitionally independent of surrounding events,
errors, internal return names, `isInternal`, lexical scope, and ADT types. -/
theorem compileStmt_ecm_independent_of_context
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (scope : List String) (adtTypes : List AdtTypeDef)
    (mod : ECM.ExternalCallModule) (args : List Expr)
    (internalFunctions : List FunctionSpec) :
    CompilationModel.compileStmt fields events errors dynamicSource internalRetNames
      isInternal scope adtTypes (Stmt.ecm mod args) internalFunctions =
    CompilationModel.compileStmt fields [] [] dynamicSource []
      false [] [] (Stmt.ecm mod args) internalFunctions := rfl

/-- Shape decomposition for `CompilationModel.compileStmt` on `Stmt.ecm mod args`
with an explicit internal-function environment: compilation succeeds only when
the argument count matches `mod.numArgs`, the arguments compile via
`compileExprListWithInternals`, and `mod.compileCanonical` succeeds on the
resulting Yul expressions. -/
theorem compileStmt_ecm_shape_with_internals
    {fields : List CompilationModel.Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {internalFunctions : List FunctionSpec}
    {mod : ECM.ExternalCallModule}
    {args : List CompilationModel.Expr}
    {compiledIR : List YulStmt}
    (hok :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (CompilationModel.Stmt.ecm mod args) internalFunctions =
          Except.ok compiledIR) :
    args.length = mod.numArgs ∧
    ∃ argExprs generated,
      CompilationModel.compileExprListWithInternals fields .calldata internalFunctions args =
        Except.ok argExprs ∧
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated := by
  simp only [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
    bind, Except.bind] at hok
  by_cases hlen : args.length = mod.numArgs
  · refine ⟨hlen, ?_⟩
    have hne : (args.length != mod.numArgs) = false := by simp [hlen]
    have hctx :
        ({ isDynamicFromCalldata := (DynamicDataSource.calldata == DynamicDataSource.calldata) } :
          ECM.CompilationContext) = { isDynamicFromCalldata := true } := rfl
    simp only [hne, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, hctx] at hok
    cases hargs :
        CompilationModel.compileExprListWithInternals fields .calldata internalFunctions args with
    | error e =>
        simp [hargs] at hok
    | ok argExprs =>
        simp only [hargs] at hok
        cases hgen :
            mod.compileCanonical { isDynamicFromCalldata := true } argExprs with
        | error e =>
            simp [hgen] at hok
        | ok generated =>
            exact ⟨argExprs, generated, rfl, hgen⟩
  · have hne : (args.length != mod.numArgs) = true := by simp [hlen]
    simp [hne, throw, Except.error] at hok

/-- Helper-free specialization of `compileStmt_ecm_shape_with_internals`. -/
theorem compileStmt_ecm_shape
    {fields : List CompilationModel.Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {mod : ECM.ExternalCallModule}
    {args : List CompilationModel.Expr}
    {compiledIR : List YulStmt}
    (hok :
      CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (CompilationModel.Stmt.ecm mod args) =
          Except.ok compiledIR) :
    args.length = mod.numArgs ∧
    ∃ argExprs generated,
      CompilationModel.compileExprList fields .calldata args =
        Except.ok argExprs ∧
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated := by
  simpa [CompilationModel.compileExprList] using
    compileStmt_ecm_shape_with_internals (internalFunctions := []) hok

/-- Layer 2 head-step bridge for an `ECM.ExternalCallModule` statement compiled
under `spec.functions`. Since `mod.compileCanonical` is user/module-supplied,
this structure isolates the module-specific source↔IR step alignment obligation
once argument arity, expression compilation, and canonical module compilation
have been extracted. -/
structure EcmHeadStepBridgeWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (mod : ECM.ExternalCallModule)
    (args : List Expr)
    (irFuelSlack : Nat := 0) : Prop where
  compile :
    ∃ compiledIR,
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR
  bridge :
    ∀ {compiledIR : List YulStmt} {argExprs : List YulExpr} {generated : List YulStmt},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR →
      args.length = mod.numArgs →
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs →
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (extraFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf compiledIR - compiledIR.length + irFuelSlack ≤ extraFuel →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.ecm mod args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.ecm mod args))
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + extraFuel + 1) state compiledIR)

/-- Construct `CompiledStmtStepWithHelpersAndHelperIRWithInternals` for
`Stmt.ecm mod args` from compilation and the module's semantic step alignment. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_ecm
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {mod : ECM.ExternalCallModule} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr} {generated : List YulStmt}
    (irFuelSlack : Nat := 0)
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) spec.functions = Except.ok compiledIR)
    (_hlen : args.length = mod.numArgs)
    (_hargCompile :
      CompilationModel.compileExprListWithInternals fields .calldata spec.functions args =
        Except.ok argExprs)
    (_hcanonical :
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated)
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState)
        (helperFuel extraFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf compiledIR - compiledIR.length + irFuelSlack ≤ extraFuel →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.ecm mod args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.ecm mod args))
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + extraFuel + 1) state compiledIR)) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope (Stmt.ecm mod args) compiledIR irFuelSlack := by
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  exact ⟨_, _, rfl, rfl,
    bridge runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack⟩

/-- Package an `EcmHeadStepBridgeWithInternals` into the Layer 2
`CompiledStmtStepWithHelpersAndHelperIRWithInternals` head-step interface,
automatically extracting the `Stmt.ecm` shape invariants from `compile`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_of_ecmBridge
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {mod : ECM.ExternalCallModule} {args : List Expr}
    {irFuelSlack : Nat}
    (hbridge :
      EcmHeadStepBridgeWithInternals
        runtimeContract spec fields scope mod args irFuelSlack) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope (Stmt.ecm mod args) compiledIR irFuelSlack := by
  rcases hbridge.compile with ⟨compiledIR, hcompile⟩
  obtain ⟨hlen, argExprs, generated, hargCompile, hcanonical⟩ :=
    compileStmt_ecm_shape_with_internals hcompile
  exact ⟨compiledIR,
    compiledStmtStepWithHelpersAndHelperIRWithInternals_ecm
      irFuelSlack hcompile hlen hargCompile hcanonical
      (hbridge.bridge hcompile hlen hargCompile hcanonical)⟩

/-- Construct `CompiledStmtStepWithHelpersAndHelperIR` for `Stmt.ecm mod args`
in the default empty-helper compilation environment. -/
theorem compiledStmtStepWithHelpersAndHelperIR_ecm
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String} {mod : ECM.ExternalCallModule} {args : List Expr}
    {compiledIR : List YulStmt} {argExprs : List YulExpr} {generated : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.ecm mod args) = Except.ok compiledIR)
    (_hlen : args.length = mod.numArgs)
    (_hargCompile :
      CompilationModel.compileExprList fields .calldata args =
        Except.ok argExprs)
    (_hcanonical :
      mod.compileCanonical { isDynamicFromCalldata := true } argExprs =
        Except.ok generated)
    (bridge :
      ∀ (runtime : SourceSemantics.RuntimeState) (state : IRState)
        (helperFuel extraFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf compiledIR - compiledIR.length ≤ extraFuel →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope (Stmt.ecm mod args))
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.ecm mod args))
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + extraFuel + 1) state compiledIR)) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope (Stmt.ecm mod args) compiledIR := by
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  exact ⟨_, _, rfl, rfl,
    bridge runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack⟩

end Compiler.Proofs.IRGeneration
