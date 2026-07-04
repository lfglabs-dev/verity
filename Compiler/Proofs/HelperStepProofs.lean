import Compiler.Proofs.IRGeneration.GenericInduction
import Compiler.Proofs.IRGeneration.SourceSemantics

/-!
# Helper Step Interface Proofs (Phase 1)

This module provides the infrastructure for constructing
`CompiledStmtStepWithHelpersAndHelperIR` witnesses for each of the four
helper-surface statement families:

1. Direct void helper calls (`Stmt.internalCall`)
2. Direct helper call with return binding (`Stmt.internalCallAssign`)
3. Expression-position helper calls (expr containing `Expr.internalCall`)
4. Structural helper transport (`Stmt.ite` / `Stmt.forEach` with helpers)

## Architecture

The four narrow step interfaces are already defined and assembled in
`GenericInduction.lean`. The assembly chain is:

```
StmtListDirectInternalHelperCallStepInterface
  + StmtListDirectInternalHelperAssignStepInterface
  → StmtListDirectInternalHelperStepInterface
    + StmtListExprInternalHelperStepInterface
    + StmtListStructuralInternalHelperStepInterface
    → StmtListInternalHelperSurfaceStepInterface
      + StmtListResidualHelperSurfaceStepInterface
      → StmtListHelperSurfaceStepInterface
        + StmtListHelperFreeStepInterface
        + StmtListHelperFreeCompiledCallsDisjoint
        → StmtListGenericWithHelpersAndHelperIR
```

## Proof strategy for each interface

### Direct void calls (`StmtListDirectInternalHelperCallStepInterface`)

Target: `Stmt.internalCall calleeName args` where
`stmtTouchesDirectInternalHelperCallSurface stmt = true`.

1. **compileOk**: `compileStmt` produces a Yul call expression statement.
2. **preserves**: Source `execStmtWithHelpers` dispatches to
   `interpretInternalFunctionFuel`; IR `execIRStmtsWithInternals` dispatches
   through `evalIRCallWithInternals`; bridge via summary postcondition.

### Direct assign calls (`StmtListDirectInternalHelperAssignStepInterface`)

Same as void calls plus return-value binding in source and Yul let-binding.

### Expression-position helpers (`StmtListExprInternalHelperStepInterface`)

Key: `InternalHelperSummaryPreservesWorldOnSuccess` ensures the helper
doesn't modify world state on success.

### Structural transport (`StmtListStructuralInternalHelperStepInterface`)

For `Stmt.ite` / `Stmt.forEach`: inductive — each branch satisfies the
list-level witness.
-/

namespace Compiler.Proofs.HelperStepProofs

open Compiler
open Compiler.CompilationModel
open Compiler.Yul
open Compiler.Proofs.IRGeneration

/-!
## Direct void internal-helper calls

The constructors below are intentionally call-only: they prove the first
non-vacuous `StmtListDirectInternalHelperCallStepInterface` witnesses while
leaving the helper-surface-closed fast paths below unchanged.  The semantic
payload is still supplied through `DirectInternalHelperCallHeadStepBridge`.
That bridge is the current architecture's exact source/IR seam: source
`execStmtWithHelpers` must be related to helper-aware compiled execution
`execIRStmtsWithInternals` after compiling the argument list.

Blocker for closing this from only `SupportedBodyHelperInterface` and
`SupportedRuntimeHelperTableInterface`: the tree has source summary soundness
(`InternalHelperSummarySound` for `interpretInternalFunctionFuel`) and IR
helper lookup/dispatch lemmas, but it does not yet expose a theorem stating
that executing a compiled internal helper body with
`execIRInternalFunctionWithInternals` satisfies the same
`InternalHelperSummaryContract.post` as the source helper.
-/

/-- Build a helper-aware singleton compiled-step proof for a direct void
internal helper call from the exact call-head bridge.  This is non-vacuous:
the `Stmt.internalCall` head is compiled and its helper-aware source/IR
execution is consumed directly from `hbridge`. -/
theorem compiledStmtStepWithHelpersAndHelperIR_internalCall_of_callHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract
        spec
        fields
        scope
        (Stmt.internalCall calleeName args)
        compiledIR := by
  rcases hbridge.compile (scope := scope) (args := args) with
    ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ := compileStmt_internalCall_shape hcompile
  have hcompileSpec :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCall calleeName args) = Except.ok compiledIR := by
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
      (hbridge.bridge
        (scope := scope)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hcompile
        hargCompile)

/-- Non-vacuous list witness for a statement list headed by
`Stmt.internalCall`.  The head proof comes from the call bridge; the tail remains
the ordinary list interface at the post-head scope. -/
theorem stmtListDirectInternalHelperCallStepInterface_cons_internalCall_of_callHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    {rest : List Stmt}
    (hbridge :
      DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName)
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
  rcases
      compiledStmtStepWithHelpersAndHelperIR_internalCall_of_callHeadStepBridge
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (calleeName := calleeName)
        (args := args)
        hbridge with
    ⟨compiledIR, hstep⟩
  exact
    stmtListDirectInternalHelperCallStepInterface_cons_internalCall
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (calleeName := calleeName)
      (args := args)
      (compiledIR := compiledIR)
      (rest := rest)
      hstep
      hrest

/-- Assemble the direct void-helper-call list interface from per-callee call
bridges for the helper names that occur in this statement list.  This is the
call-only counterpart of the broader direct-helper catalog assembly and does
not require the assign-call half. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_callHeadStepBridges
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {calleeName : String},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        DirectInternalHelperCallHeadStepBridge runtimeContract spec fields calleeName) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperCallStepInterface_of_internalCallSteps_of_helperCallNames
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      (fun {scope} {calleeName} {args} hmem =>
        compiledStmtStepWithHelpersAndHelperIR_internalCall_of_callHeadStepBridge
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (calleeName := calleeName)
          (args := args)
          (hbridge hmem))

/-!
## Direct helper-return-binding calls

These constructors mirror the direct void-call witnesses above for
`Stmt.internalCallAssign`.  They are intentionally still parameterised by
`DirectInternalHelperAssignHeadStepBridge`: that bridge is the exact missing
semantic seam for helper-return bindings, connecting source
`execStmtWithHelpers` through `interpretInternalFunctionFuel` to helper-aware
compiled execution through `execIRStmtsWithInternals` and
`evalIRCallWithInternals`.  A closed bridge should be supplied by the later
rank-decreasing helper-summary proof once the architecture exposes the needed
compiled-helper summary lemma.
-/

/-- Build a helper-aware singleton compiled-step proof for a direct helper
return binding from the exact assign-head bridge.  This is non-vacuous: the
`Stmt.internalCallAssign` head is compiled as a Yul `let` binding and its
helper-aware source/IR execution is consumed directly from `hbridge`. -/
theorem compiledStmtStepWithHelpersAndHelperIR_internalCallAssign_of_assignHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract
        spec
        fields
        scope
        (Stmt.internalCallAssign names calleeName args)
        compiledIR := by
  rcases hbridge.compile (scope := scope) (names := names) (args := args) with
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
      (hbridge.bridge
        (scope := scope)
        (names := names)
        (args := args)
        (compiledIR := compiledIR)
        (argExprs := argExprs)
        hcompile
        hargCompile)

/-- Non-vacuous list witness for a statement list headed by
`Stmt.internalCallAssign`.  The head proof comes from the assign bridge; the
tail remains the ordinary list interface at the post-head scope. -/
theorem stmtListDirectInternalHelperAssignStepInterface_cons_internalCallAssign_of_assignHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {rest : List Stmt}
    (hbridge :
      DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName)
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
  rcases
      compiledStmtStepWithHelpersAndHelperIR_internalCallAssign_of_assignHeadStepBridge
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (names := names)
        (calleeName := calleeName)
        (args := args)
        hbridge with
    ⟨compiledIR, hstep⟩
  exact
    stmtListDirectInternalHelperAssignStepInterface_cons_internalCallAssign
      hstep
      hrest

/-- Assemble the direct helper-return-binding list interface from per-callee
assign bridges for the helper names that occur in this statement list.  This is
the assign-only counterpart of the broader direct-helper catalog assembly. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_assignHeadStepBridges
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {calleeName : String},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        DirectInternalHelperAssignHeadStepBridge runtimeContract spec fields calleeName) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperAssignStepInterface_of_internalCallAssignSteps_of_helperCallNames
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      (fun {scope} {names} {calleeName} {args} hmem =>
        compiledStmtStepWithHelpersAndHelperIR_internalCallAssign_of_assignHeadStepBridge
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (names := names)
          (calleeName := calleeName)
          (args := args)
          (hbridge hmem))

/-- Assemble the direct helper-return-binding list interface for a function
body from the per-callee assign bridge catalog used by the rank-decreasing
helper-summary layer. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_perCalleeAssignBridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {fn : FunctionSpec}
    (hbridge :
      DirectInternalHelperPerCalleeAssignBridgeCatalog runtimeContract spec fields fn) :
    StmtListDirectInternalHelperAssignStepInterface
      runtimeContract spec fields scope fn.body := by
  exact
    stmtListDirectInternalHelperAssignStepInterface_of_assignHeadStepBridges
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := fn.body)
      (fun {calleeName} hmem =>
        hbridge.assign (by simpa [helperCallNames] using hmem))

/-!
## Expression-position internal-helper calls

Expression-position helper calls are statement-head obligations: the source
expression evaluator runs helpers through `evalExprWithHelpers` and
`interpretInternalFunctionFuel`, while the compiled statement can run helper
calls through `evalIRCallWithInternals` under `execIRStmtsWithInternals`.

The bridge below is intentionally the same narrow shape as the direct-call and
direct-assign bridges above.  It is non-vacuous at the interface level: when a
statement head has `stmtTouchesExprInternalHelperSurface = true`, the list
interface consumes an exact helper-aware compiled statement step for that head.
Closing the bridge from `InternalHelperSummaryContract` still requires one
missing API theorem: a compositional expression-context lemma connecting
`SourceSemantics.evalExprWithHelpers` internal-call summary results and
world-preservation evidence to the corresponding compiled Yul expression
evaluation under `evalIRCallWithInternals`.
-/

/-- Compiled-helper lookup specialized to helper-aware Yul expression calls.
This is the expression-context counterpart of the statement-call shape lemmas
for `execIRStmtsWithInternals`: after the argument expressions evaluate, the
call dispatches through the internal helper table supplied by
`SupportedCompiledInternalHelperWitness`. -/
theorem evalIRCallWithInternals_of_compiledHelperWitness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {calleeName : String}
    (compiledHelper :
      SupportedCompiledInternalHelperWitness spec runtimeContract calleeName)
    (state : IRState)
    (irFuel : Nat)
    {argExprs : List YulExpr}
    {argVals : List Nat}
    {state' : IRState}
    (hargs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state') :
    ∃ helper,
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      evalIRCallWithInternals runtimeContract (irFuel + 1) state
          (CompilationModel.internalFunctionYulName calleeName) argExprs =
        execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals := by
  have hcalleeName : compiledHelper.sourceWitness.callee.name = calleeName :=
    compiledHelper.sourceWitness.nameEq
  have hfindSome :
      (findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName)).isSome = true := by
    simpa [hcalleeName] using
      (findInternalFunction?_of_compileInternalFunction_mem
        compiledHelper.compileOk
        compiledHelper.presentInRuntime)
  cases hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) with
  | none =>
      simp [hfind] at hfindSome
  | some helper =>
      refine ⟨helper, rfl, ?_⟩
      simp [evalIRCallWithInternals, hargs, hfind]

/-- Per-callee expression-context helper bridge. It binds together the source
summary evidence used by `evalExprWithHelpers` and the compiled-helper witness
used by `evalIRCallWithInternals`. The remaining non-closed obligation is still
compositional expression compilation: callers must prove that their compiled
Yul argument expressions evaluate to the same `argVals` in the corresponding IR
state. -/
structure ExprInternalHelperCallContextBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (calleeName : String) where
  sourceWitness :
    SupportedInternalHelperWitness spec calleeName
  summarySound :
    SourceSemantics.InternalHelperSummarySound
      spec sourceWitness.callee sourceWitness.summary.contract
  sourcePreservesWorld :
    InternalHelperSummaryPreservesWorldOnSuccess sourceWitness.summary.contract
  compiledHelper :
    SupportedCompiledInternalHelperWitness spec runtimeContract calleeName
  irCall :
    ∀ (state : IRState) (irFuel : Nat)
      {argExprs : List YulExpr} {argVals : List Nat} {state' : IRState},
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
          .values argVals state' →
      ∃ helper,
        findInternalFunction? runtimeContract
          (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
        evalIRCallWithInternals runtimeContract (irFuel + 1) state
            (CompilationModel.internalFunctionYulName calleeName) argExprs =
          execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals

/-- Construct the per-callee expression-context bridge from the current supported
helper inventory: source summary soundness, expression-call world preservation,
and the compiled runtime helper table. -/
def exprInternalHelperCallContextBridge_of_supportedEvidence
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hSummaries : SourceSemantics.SupportedBodyHelperSummariesSound spec fn hHelpers)
    (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
    {calleeName : String}
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    ExprInternalHelperCallContextBridge runtimeContract spec calleeName := by
  let hcall : calleeName ∈ helperCallNames fn :=
    exprHelperCallNames_subset_helperCallNames hmem
  let witness := hHelpers.summaryOfCall hcall
  refine
    { sourceWitness := witness
      summarySound :=
        SourceSemantics.SupportedBodyHelperInterface.summarySoundOfCall
          hHelpers hSummaries hcall
      sourcePreservesWorld := hHelpers.exprSummaryPreservesWorld hmem
      compiledHelper := hRuntime.compiledOfCall hHelpers hcall
      irCall := ?_ }
  intro state irFuel argExprs argVals state' hargs
  exact
    evalIRCallWithInternals_of_compiledHelperWitness
      (runtimeContract := runtimeContract)
      (spec := spec)
      (calleeName := calleeName)
      (hRuntime.compiledOfCall hHelpers hcall)
      state
      irFuel
      hargs

/-- Source half of the expression-context bridge for an expression-position
helper call. It simultaneously exposes the `evalExprWithHelpers` reduction, the
`InternalHelperSummaryContract.post` fact for the underlying
`interpretInternalFunctionFuel`, and the world-preservation consequence used by
expression contexts. -/
theorem exprInternalHelperCallContextBridge_sourceEvidence
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {calleeName : String}
    {args : List Expr}
    (hctx : ExprInternalHelperCallContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    {fuel : Nat}
    {state : SourceSemantics.RuntimeState}
    {argVals : List Nat}
    (hargs :
      SourceSemantics.evalExprListWithHelpers spec fields (fuel + 1) state args =
        some argVals) :
    let result :=
      SourceSemantics.interpretInternalFunctionFuel
        spec fuel hctx.sourceWitness.callee state.world argVals
    SourceSemantics.evalExprWithHelpers spec fields (fuel + 1) state
        (Expr.internalCall calleeName args) =
          (if result.success then result.returnValue else none) ∧
      hctx.sourceWitness.summary.contract.post fuel state.world argVals
        result.success result.returnValue result.world ∧
      (result.success = true → result.world = state.world) := by
  intro result
  refine ⟨?_, ?_, ?_⟩
  · simp +zetaDelta [
      SourceSemantics.evalExprWithHelpers_internalCall_of_witness
        hctx.sourceWitness hnodup,
      hargs]
  · exact hctx.summarySound fuel state.world argVals
  · intro hsuccess
    exact SourceSemantics.helperSummaryPreservesWorldOnSuccess
      hctx.sourcePreservesWorld
      (hpost := hctx.summarySound fuel state.world argVals)
      hsuccess

/-- Compiler shape for an expression-position internal helper call.  The
argument expressions are the exact output of `compileInternalCallArgs`, which is
more general than `compileExprListWithInternals`: internal helper parameters may
expand direct forwarded source arguments into several Yul arguments. -/
theorem compileExprWithInternals_internalCall_shape
    {fields : List Field}
    {dynamicSource : DynamicDataSource}
    {internalFunctions : List FunctionSpec}
    {calleeName : String}
    {args : List Expr}
    {argExprs : List YulExpr}
    (hargs :
      CompilationModel.compileInternalCallArgs fields dynamicSource internalFunctions calleeName args =
        Except.ok argExprs) :
    CompilationModel.compileExprWithInternals fields dynamicSource internalFunctions
        (Expr.internalCall calleeName args) =
      Except.ok
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) := by
  simp [CompilationModel.compileExprWithInternals, hargs]

/-- Result package for composing an expression-position internal helper call
through source evaluation, expression compilation, compiled argument evaluation,
and helper-aware IR dispatch.  It is factored out so the public theorem below
stays below the proof-length gate while still exposing every piece of evidence
needed by the later statement-head bridge. -/
def ExprInternalHelperCompiledCallContextResult
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (calleeName : String)
    (args : List Expr)
    (hctx : ExprInternalHelperCallContextBridge runtimeContract spec calleeName)
    (helperFuel irFuel : Nat)
    (runtime : SourceSemantics.RuntimeState)
    (state state' : IRState)
    (argVals : List Nat)
    (argExprs : List YulExpr) : Prop :=
  let sourceResult :=
    SourceSemantics.interpretInternalFunctionFuel
      spec helperFuel hctx.sourceWitness.callee runtime.world argVals
  ∃ helper,
    CompilationModel.compileExprWithInternals fields .calldata spec.functions
        (Expr.internalCall calleeName args) =
      Except.ok
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) ∧
    SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
        (Expr.internalCall calleeName args) =
      (if sourceResult.success then sourceResult.returnValue else none) ∧
    hctx.sourceWitness.summary.contract.post helperFuel runtime.world argVals
      sourceResult.success sourceResult.returnValue sourceResult.world ∧
    (sourceResult.success = true → sourceResult.world = runtime.world) ∧
    findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
    evalIRCallWithInternals runtimeContract (irFuel + 1) state
        (CompilationModel.internalFunctionYulName calleeName) argExprs =
      execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals ∧
    evalIRExprWithInternals runtimeContract (irFuel + 1) state
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) =
      match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
      | .values [value] state'' => .value value state''
      | .values _ state'' => .revert state''
      | .stop state'' => .stop state''
      | .return value state'' => .return value state''
      | .revert state'' => .revert state''

/-- Lift an already-proved helper-aware call dispatch equality through
`evalIRExprWithInternals` for the compiled call expression. -/
theorem evalIRExprWithInternals_call_of_dispatch
    (runtimeContract : IRContract)
    (irFuel : Nat)
    (state state' : IRState)
    (calleeName : String)
    (argExprs : List YulExpr)
    (helper : IRInternalFunctionDef)
    (argVals : List Nat)
    (hirDispatch :
      evalIRCallWithInternals runtimeContract (irFuel + 1) state
          (CompilationModel.internalFunctionYulName calleeName) argExprs =
        execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals) :
    evalIRExprWithInternals runtimeContract (irFuel + 1) state
        (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) =
      match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
      | .values [value] state'' => .value value state''
      | .values _ state'' => .revert state''
      | .stop state'' => .stop state''
      | .return value state'' => .return value state''
      | .revert state'' => .revert state'' := by
  rw [evalIRExprWithInternals_call, hirDispatch]
  cases execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
  | values values state'' =>
      cases values with
      | nil => rfl
      | cons value rest => cases rest <;> rfl
  | stop state'' => rfl
  | «return» value state'' => rfl
  | revert state'' => rfl

/-- Compose the phase-4 per-callee expression helper bridge with the expression
compiler at the helper-call head.  This theorem is the current non-vacuous
compiler/context handoff: once callers prove that the compiled Yul argument
context evaluates to the same helper argument values as source
`evalExprListWithHelpers`, the bridge supplies source summary soundness,
helper-world preservation on success, compiled helper lookup/dispatch through
`evalIRCallWithInternals`, and the corresponding `evalIRExprWithInternals`
shape for the compiled call expression.

This intentionally remains at the `Expr.internalCall` head.  Lifting it through
arbitrary parent expressions and then through statement heads still requires a
separate compositional expression compiler theorem relating
`evalExprWithHelpers` and `evalIRExprWithInternals` for non-call expression
contexts while preserving the helper-world and argument-evaluation evidence. -/
theorem exprInternalHelperCallContextBridge_compileExprWithInternals_internalCall
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {calleeName : String}
    {args : List Expr}
    (hctx : ExprInternalHelperCallContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    {helperFuel irFuel : Nat}
    {runtime : SourceSemantics.RuntimeState}
    {state state' : IRState}
    {argVals : List Nat}
    {argExprs : List YulExpr}
    (hsourceArgs :
      SourceSemantics.evalExprListWithHelpers spec fields (helperFuel + 1) runtime args =
        some argVals)
    (hcompileArgs :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions calleeName args =
        Except.ok argExprs)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state') :
    ExprInternalHelperCompiledCallContextResult runtimeContract spec fields
      calleeName args hctx helperFuel irFuel runtime state state' argVals argExprs := by
  unfold ExprInternalHelperCompiledCallContextResult
  dsimp only
  have hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.internalCall calleeName args) =
        Except.ok
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) :=
    compileExprWithInternals_internalCall_shape hcompileArgs
  have hsource :=
    exprInternalHelperCallContextBridge_sourceEvidence (runtimeContract := runtimeContract)
      (spec := spec) (fields := fields) (calleeName := calleeName) (args := args)
      hctx hnodup (fuel := helperFuel) (state := runtime) hsourceArgs
  have hirCall := hctx.irCall state irFuel hirArgs
  rcases hirCall with ⟨helper, hfind, hirDispatch⟩
  refine ⟨helper, hcompile, ?_, ?_, ?_, hfind, hirDispatch, ?_⟩
  · exact hsource.1
  · exact hsource.2.1
  · exact hsource.2.2
  · exact evalIRExprWithInternals_call_of_dispatch
      runtimeContract irFuel state state' calleeName argExprs helper argVals hirDispatch

/-- Expression-context payload that combines outer expression correspondence
with the exact phase-5 helper-head evidence. The remaining blocker is the
recursive non-call `Expr` theorem that constructs this package for contexts. -/
def ExprInternalHelperCompositionalContextResult
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (expr : Expr)
    (exprIR : YulExpr)
    (helperFuel irFuel : Nat)
    (runtime headRuntime : SourceSemantics.RuntimeState)
    (state headState finalState : IRState)
    (value : Nat) : Prop :=
  CompilationModel.compileExprWithInternals fields .calldata spec.functions expr =
      Except.ok exprIR ∧
    SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime expr =
      some value ∧
    evalIRExprWithInternals runtimeContract (irFuel + 1) state exprIR =
      .value value finalState ∧
    FunctionBody.runtimeStateMatchesIR fields headRuntime headState ∧
    ∃ (calleeName : String) (args : List Expr)
        (hctx : ExprInternalHelperCallContextBridge runtimeContract spec calleeName)
        (argVals : List Nat) (argExprs : List YulExpr) (argState : IRState),
      ExprInternalHelperCompiledCallContextResult runtimeContract spec fields
        calleeName args hctx helperFuel irFuel headRuntime headState argState
        argVals argExprs

/-- Direct-head base case for the compositional expression-context payload. -/
theorem exprInternalHelperCompositionalContextResult_internalCall_head
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {calleeName : String} {args : List Expr}
    (hctx : ExprInternalHelperCallContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    {helperFuel irFuel : Nat} {runtime : SourceSemantics.RuntimeState}
    {state argState finalState : IRState} {argVals : List Nat}
    {argExprs : List YulExpr} {value : Nat}
    (hruntime : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (hsourceArgs :
      SourceSemantics.evalExprListWithHelpers spec fields (helperFuel + 1) runtime args =
        some argVals)
    (hcompileArgs :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions calleeName args =
        Except.ok argExprs)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals argState)
    (hsourceValue :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
          (Expr.internalCall calleeName args) =
        some value)
    (hirValue :
      evalIRExprWithInternals runtimeContract (irFuel + 1) state
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs) =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.internalCall calleeName args)
      (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)
      helperFuel irFuel runtime runtime state state finalState value := by
  unfold ExprInternalHelperCompositionalContextResult
  refine ⟨?_, hsourceValue, hirValue, hruntime, ?_⟩
  · exact compileExprWithInternals_internalCall_shape hcompileArgs
  · refine ⟨calleeName, args, hctx, argVals, argExprs, argState, ?_⟩
    exact
      exprInternalHelperCallContextBridge_compileExprWithInternals_internalCall
        (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
        (calleeName := calleeName) (args := args) hctx hnodup
        (helperFuel := helperFuel) (irFuel := irFuel) (runtime := runtime)
        (state := state) (state' := argState) (argVals := argVals)
        (argExprs := argExprs) hsourceArgs hcompileArgs hirArgs

/-- Expression-helper statement-head bridge. Future helper-summary induction
should construct this for each statement head whose helper work appears in
expression position. The semantic payload is the exact helper-aware source/IR
step needed by `CompiledStmtStepWithHelpersAndHelperIR`; this file only packages
that payload into the split statement-list interface. -/
structure ExprInternalHelperHeadStepBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (stmt : Stmt) : Prop where
  compile :
    ∀ {scope : List String},
      ∃ compiledIR,
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
          Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {compiledIR : List YulStmt},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
        Except.ok compiledIR →
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
          (stmtNextScope scope stmt)
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt)
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + irFuel + 1) state compiledIR)

/-- Build a helper-aware singleton statement proof for an expression-position
helper head from the exact expression-head bridge. -/
theorem compiledStmtStepWithHelpersAndHelperIR_of_exprHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    (hbridge :
      ExprInternalHelperHeadStepBridge runtimeContract spec fields stmt) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract
        spec
        fields
        scope
        stmt
        compiledIR := by
  rcases hbridge.compile (scope := scope) with ⟨compiledIR, hcompile⟩
  have hcompileSpec :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
        Except.ok compiledIR := by
    exact hcompile
  refine ⟨compiledIR, ?_⟩
  refine { compileOk := hcompileSpec, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  exact
    ⟨_,
      _,
      rfl,
      rfl,
      hbridge.bridge
        (scope := scope)
        (compiledIR := compiledIR)
        hcompile
        runtime
        state
        helperFuel
        extraFuel
        hfuelPos
        hexact
        hscope
        hbounded
        hruntime⟩

/-- Non-vacuous list witness for a statement list whose head contains
expression-position helper work. The head proof comes from the expression-head
bridge; the tail remains the ordinary expression-helper list interface at the
post-head scope. -/
theorem stmtListExprInternalHelperStepInterface_cons_of_exprHeadStepBridge
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    (hbridge :
      ExprInternalHelperHeadStepBridge runtimeContract spec fields stmt)
    (hrest :
      StmtListExprInternalHelperStepInterface
        runtimeContract
        spec
        fields
        (stmtNextScope scope stmt)
        rest) :
    StmtListExprInternalHelperStepInterface
      runtimeContract
      spec
      fields
      scope
      (stmt :: rest) := by
  rcases
      compiledStmtStepWithHelpersAndHelperIR_of_exprHeadStepBridge
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmt := stmt)
        hbridge with
    ⟨compiledIR, hstep⟩
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Assemble the expression-position helper list interface from exact bridges
for the expression-helper heads that occur in this statement list. This keeps
the recursion mechanical and leaves the semantic source/IR helper-summary
alignment localized to `ExprInternalHelperHeadStepBridge`. -/
theorem stmtListExprInternalHelperStepInterface_of_exprHeadStepBridges
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {stmt : Stmt},
        stmt ∈ stmts →
        stmtTouchesExprInternalHelperSurface stmt = true →
        ExprInternalHelperHeadStepBridge runtimeContract spec fields stmt) :
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hexpr
        exact
          compiledStmtStepWithHelpersAndHelperIR_of_exprHeadStepBridge
            (runtimeContract := runtimeContract)
            (spec := spec)
            (fields := fields)
            (scope := scope)
            (stmt := stmt)
            (hbridge (by simp) hexpr)
      · apply ih
        intro stmt' hmem hexpr
        exact hbridge (List.mem_cons_of_mem _ hmem) hexpr

/-- For helper-surface-closed statement lists, the four narrow helper-step
interfaces are all trivially satisfied. This is the entry point for contracts
that do not use internal helpers at all. -/
theorem allHelperInterfacesSatisfied_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts ∧
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts ∧
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts ∧
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts :=
  ⟨stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed hsurface,
   stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed hsurface,
   stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed hsurface,
   stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed hsurface⟩

/-- Full assembly from the four narrow interfaces plus helper-free and residual
interfaces into the whole-statement-list-level witness. This is the top-level
composition theorem that the function-level proof consumes. -/
theorem fullHelperAwareListWitness_of_allInterfaces
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    hhelperFree hcall hassign hexpr hstruct hresidual hlegacy hnoEvents hnoErrors hnoInternalFunctions

/-- Convenience alias: full assembly using the disjoint-calls variant (for
contracts where the IR contract has internal functions but compiled IR calls
are disjoint from the internal table). Unlike the legacy-compatible variant,
this does not require `runtimeContract.internalFunctions = []`. -/
theorem fullHelperAwareListWitness_of_allInterfaces_disjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    hhelperFree
    (stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
      (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
        (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
          hcall hassign)
        hexpr hstruct)
      hresidual)
    hnoEvents
    hnoErrors
    hdisjoint

/-- Fast-path for helper-free contracts: if the statement list doesn't touch
the helper surface at all, all five interfaces are vacuously satisfied and we
can go straight to the whole-list proof with just the helper-free step interface
and legacy compatibility. -/
theorem helperFreeContractWitness
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  let ⟨hcall, hassign, hexpr, hstruct⟩ :=
    allHelperInterfacesSatisfied_of_helperSurfaceClosed hsurface
  fullHelperAwareListWitness_of_allInterfaces
    hhelperFree hcall hassign hexpr hstruct
    (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed hsurface)
    hlegacy hnoEvents hnoErrors hnoInternalFunctions

/-- Fast-path using disjoint-calls variant for helper-free contracts with
non-empty internal function tables. -/
theorem helperFreeContractWitness_disjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts :=
  let ⟨hcall, hassign, hexpr, hstruct⟩ :=
    allHelperInterfacesSatisfied_of_helperSurfaceClosed hsurface
  fullHelperAwareListWitness_of_allInterfaces_disjoint
    hhelperFree hcall hassign hexpr hstruct
    (stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed hsurface)
    hnoEvents
    hnoErrors
    hdisjoint

end Compiler.Proofs.HelperStepProofs
