import Compiler.Proofs.IRGeneration.GenericInduction
import Compiler.Proofs.IRGeneration.HelperBodyBridge
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

/-- Build a spec-functions-aware helper-aware singleton compiled-step proof for
a direct void internal helper call from the exact `WithInternals` call-head
bridge. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_callHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperCallHeadStepBridgeWithInternals runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract
        spec
        fields
        scope
        (Stmt.internalCall calleeName args)
        compiledIR := by
  rcases hbridge.compile (scope := scope) (args := args) with
    ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ :=
    compileStmt_internalCall_shape_with_internals hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (calleeName := calleeName)
      (args := args)
      (compiledIR := compiledIR)
      (argExprs := argExprs)
      hcompile
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

/-- Non-vacuous `WithInternals` list witness for a statement list headed by
`Stmt.internalCall`. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_cons_internalCall_of_callHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {calleeName : String}
    {args : List Expr}
    {rest : List Stmt}
    (hbridge :
      DirectInternalHelperCallHeadStepBridgeWithInternals runtimeContract spec fields calleeName)
    (hrest :
      StmtListDirectInternalHelperCallStepInterfaceWithInternals
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        rest) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCall calleeName args :: rest) := by
  rcases
      compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_callHeadStepBridgeWithInternals
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (calleeName := calleeName)
        (args := args)
        hbridge with
    ⟨compiledIR, hstep⟩
  exact
    stmtListDirectInternalHelperCallStepInterfaceWithInternals_cons_internalCall
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

/-- Assemble the spec-functions-aware direct void-helper-call list interface
from per-callee `WithInternals` call bridges for helper names in the list. -/
theorem stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_callHeadStepBridgesWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {calleeName : String},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        DirectInternalHelperCallHeadStepBridgeWithInternals runtimeContract spec fields calleeName) :
    StmtListDirectInternalHelperCallStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperCallStepInterfaceWithInternals_of_internalCallSteps_of_helperCallNames
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      (fun {scope} {calleeName} {args} hmem =>
        compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_callHeadStepBridgeWithInternals
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

/-- Build a spec-functions-aware helper-aware singleton compiled-step proof for
a direct helper return binding from the exact `WithInternals` assign-head
bridge. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_assignHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (hbridge :
      DirectInternalHelperAssignHeadStepBridgeWithInternals runtimeContract spec fields calleeName) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract
        spec
        fields
        scope
        (Stmt.internalCallAssign names calleeName args)
        compiledIR := by
  rcases hbridge.compile (scope := scope) (names := names) (args := args) with
    ⟨compiledIR, hcompile⟩
  obtain ⟨argExprs, hargCompile, _⟩ :=
    compileStmt_internalCallAssign_shape_with_internals hcompile
  refine ⟨compiledIR, ?_⟩
  exact
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign
      hcompile
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

/-- Non-vacuous `WithInternals` list witness for a statement list headed by
`Stmt.internalCallAssign`. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_cons_internalCallAssign_of_assignHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {rest : List Stmt}
    (hbridge :
      DirectInternalHelperAssignHeadStepBridgeWithInternals runtimeContract spec fields calleeName)
    (hrest :
      StmtListDirectInternalHelperAssignStepInterfaceWithInternals
        runtimeContract
        spec
        fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        rest) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract
      spec
      fields
      scope
      (Stmt.internalCallAssign names calleeName args :: rest) := by
  rcases
      compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_assignHeadStepBridgeWithInternals
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
    stmtListDirectInternalHelperAssignStepInterfaceWithInternals_cons_internalCallAssign
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

/-- Assemble the spec-functions-aware direct helper-return-binding list
interface from per-callee `WithInternals` assign bridges. -/
theorem stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_assignHeadStepBridgesWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {calleeName : String},
        calleeName ∈ (stmtListInternalHelperCallNames stmts).eraseDups →
        DirectInternalHelperAssignHeadStepBridgeWithInternals runtimeContract spec fields calleeName) :
    StmtListDirectInternalHelperAssignStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperAssignStepInterfaceWithInternals_of_internalCallAssignSteps_of_helperCallNames
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      (fun {scope} {names} {calleeName} {args} hmem =>
        compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_assignHeadStepBridgeWithInternals
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
### Direct statement helper context bridge

This package is the supported-evidence handoff for direct statement-position
helper calls. It does not prove the final head-step bridge by itself: the
remaining statement proof must still align source and IR argument evaluation and
discharge the helper-body execution context consumed by
`execIRInternalFunctionWithInternals_obeys_internal_helper_summary`.
-/

/-- Direct-statement helper context bridge assembled from the currently exposed
supported-helper APIs. It packages the source summary evidence and the compiled
helper dispatch facts for both direct void calls and return-binding calls. -/
structure DirectInternalHelperStatementContextBridge
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (calleeName : String) where
  sourceWitness :
    SupportedInternalHelperWitness spec calleeName
  summarySound :
    SourceSemantics.InternalHelperSummarySound
      spec sourceWitness.callee sourceWitness.summary.contract
  compiledHelper :
    SupportedCompiledInternalHelperWitness spec runtimeContract calleeName
  irCallDispatch :
    ∀ {fields : List Field} {scope : List String} {args : List Expr}
      {compiledIR : List YulStmt} {argExprs : List YulExpr}
      (state : IRState) (irFuel : Nat)
      {argVals : List Nat} {state' : IRState},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCall calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state' →
      ∃ helper,
        compiledIR = [YulStmt.exprStmt
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
        findInternalFunction? runtimeContract
          (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
        execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
          match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
          | .values _ state'' => .continue state''
          | .stop state'' => .stop state''
          | .return value' state'' => .return value' state''
          | .revert state'' => .revert state''
  irAssignDispatch :
    ∀ {fields : List Field} {scope : List String} {names : List String}
      {args : List Expr} {compiledIR : List YulStmt} {argExprs : List YulExpr}
      (state : IRState) (irFuel : Nat)
      {argVals : List Nat} {state' : IRState},
      CompilationModel.compileStmt fields [] [] .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) = Except.ok compiledIR →
      CompilationModel.compileExprList fields .calldata args = Except.ok argExprs →
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals state' →
      ∃ helper,
        compiledIR = [YulStmt.letMany names
          (YulExpr.call (CompilationModel.internalFunctionYulName calleeName) argExprs)] ∧
        findInternalFunction? runtimeContract
          (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
        execIRStmtsWithInternals runtimeContract (irFuel + 3) state compiledIR =
          match execIRInternalFunctionWithInternals runtimeContract irFuel state' helper argVals with
          | .values values state'' =>
              if names.length = values.length then
                .continue (state''.setVars (names.zip values))
              else .revert state''
          | .stop state'' => .stop state''
          | .return value' state'' => .return value' state''
          | .revert state'' => .revert state''

/-- Instantiate the direct-statement helper context bridge from the supported
helper inventory for a callee that appears in `helperCallNames fn`. -/
def directInternalHelperStatementContextBridge_of_supportedEvidence
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hSummaries : SourceSemantics.SupportedBodyHelperSummariesSound spec fn hHelpers)
    (hRuntime : SupportedRuntimeHelperTableInterface spec runtimeContract)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    DirectInternalHelperStatementContextBridge runtimeContract spec calleeName := by
  let witness := hHelpers.summaryOfCall hmem
  let compiledHelper := hRuntime.compiledOfCall hHelpers hmem
  refine
    { sourceWitness := witness
      summarySound :=
        SourceSemantics.SupportedBodyHelperInterface.summarySoundOfCall
          hHelpers hSummaries hmem
      compiledHelper := compiledHelper
      irCallDispatch := ?_
      irAssignDispatch := ?_ }
  · intro fields scope args compiledIR argExprs state irFuel argVals state'
      hcompile hargCompile hargs
    exact
      execIRStmtsWithInternals_of_internalCall_compiledHelperWitness
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        compiledHelper
        state
        irFuel
        hcompile
        argExprs
        hargCompile
        hargs
  · intro fields scope names args compiledIR argExprs state irFuel argVals state'
      hcompile hargCompile hargs
    exact
      execIRStmtsWithInternals_of_internalCallAssign_compiledHelperWitness
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (names := names)
        (calleeName := calleeName)
        (args := args)
        (compiledIR := compiledIR)
        compiledHelper
        state
        irFuel
        hcompile
        argExprs
        hargCompile
        hargs

/-- Source-side evidence for a direct void helper call from the packaged
statement context bridge: the source statement reduces through the supported
callee witness and the callee summary post holds for the same helper result. -/
theorem directInternalHelperStatementContextBridge_sourceCallEvidence
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {calleeName : String}
    {args : List Expr}
    (hctx :
      DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
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
    SourceSemantics.execStmtWithHelpers spec fields (fuel + 1) state
        (Stmt.internalCall calleeName args) =
          (if result.success then
            .continue { state with world := result.world }
          else .revert) ∧
      hctx.sourceWitness.summary.contract.post fuel state.world argVals
        result.success result.returnValue result.world := by
  intro result
  refine ⟨?_, ?_⟩
  · simpa [result, hargs] using
      SourceSemantics.execStmtWithHelpers_internalCall_of_witness
        (spec := spec)
        (fields := fields)
        (fuel := fuel)
        (state := state)
        (calleeName := calleeName)
        (args := args)
        hctx.sourceWitness
        hnodup
  · simpa [result] using hctx.summarySound fuel state.world argVals

abbrev directInternalHelperAssignSourceResult
    (state : SourceSemantics.RuntimeState)
    (names : List String)
    (result : SourceSemantics.InternalFunctionResult) :
    SourceSemantics.StmtResult :=
  if result.success then
    match names, result.returnValue with
    | [name], some value =>
        .continue
          { world := result.world
            bindings := SourceSemantics.bindValue state.bindings name value }
    | _, _ => .revert
  else .revert

abbrev DirectInternalHelperAssignSourceEvidence
    {runtimeContract : IRContract} {spec : CompilationModel}
    (fields : List Field) {calleeName : String} (names : List String) (args : List Expr)
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (fuel : Nat) (state : SourceSemantics.RuntimeState) (argVals : List Nat) : Prop :=
  let result := SourceSemantics.interpretInternalFunctionFuel
    spec fuel hctx.sourceWitness.callee state.world argVals
  SourceSemantics.execStmtWithHelpers spec fields (fuel + 1) state
      (Stmt.internalCallAssign names calleeName args) =
        directInternalHelperAssignSourceResult state names result ∧
    hctx.sourceWitness.summary.contract.post fuel state.world argVals
      result.success result.returnValue result.world

/-- Source-side evidence for a direct helper return-binding call from the
packaged statement context bridge. -/
theorem directInternalHelperStatementContextBridge_sourceAssignEvidence
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {calleeName : String} {names : List String} {args : List Expr}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    {fuel : Nat} {state : SourceSemantics.RuntimeState} {argVals : List Nat}
    (hargs :
      SourceSemantics.evalExprListWithHelpers spec fields (fuel + 1) state args =
        some argVals) :
    DirectInternalHelperAssignSourceEvidence fields names args hctx fuel state argVals := by
  dsimp [DirectInternalHelperAssignSourceEvidence]
  refine ⟨?_, ?_⟩
  · simpa [hargs, directInternalHelperAssignSourceResult] using
      SourceSemantics.execStmtWithHelpers_internalCallAssign_of_witness
        (spec := spec)
        (fields := fields)
        (fuel := fuel)
        (state := state)
        (names := names)
        (calleeName := calleeName)
        (args := args)
        hctx.sourceWitness
        hnodup
  · simpa using hctx.summarySound fuel state.world argVals

abbrev directInternalHelperCallSourceResult
    (state : SourceSemantics.RuntimeState)
    (result : SourceSemantics.InternalFunctionResult) :
    SourceSemantics.StmtResult :=
  if result.success then
    .continue { state with world := result.world }
  else .revert

abbrev directInternalHelperCallIRResult
    (callerState : IRState) (helper : IRInternalFunctionDef)
    (bodyResult : IRExecResultWithInternals) :
    IRExecResultWithInternals :=
  match internalHelperBodyIRExecResultAsCallResult callerState helper bodyResult with
  | .values _ state' => .continue state'
  | .stop state' => .stop state'
  | .return value state' => .return value state'
  | .revert state' => .revert state'

/-- The remaining direct void-call summary obligation after source reduction and
the N1a/N2/N3 IR helper-summary bridge have been applied.  Downstream proofs must
turn the helper summary post into the concrete statement-step source/IR state
relation required by `stmtStepMatchesIRExecWithInternals`. -/
abbrev DirectInternalHelperCallSummaryStepPostcondition
    {runtimeContract : IRContract} {spec : CompilationModel}
    (fields : List Field) (nextScope : List String)
    {calleeName : String}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (helperFuel : Nat)
    (runtime : SourceSemantics.RuntimeState)
    (argVals : List Nat)
    (callerState : IRState)
    (helper : IRInternalFunctionDef)
    (bodyResult : IRExecResultWithInternals) : Prop :=
  let sourceResult :=
    SourceSemantics.interpretInternalFunctionFuel
      spec helperFuel hctx.sourceWitness.callee runtime.world argVals
  hctx.sourceWitness.summary.contract.post helperFuel runtime.world argVals
      sourceResult.success sourceResult.returnValue sourceResult.world →
    stmtStepMatchesIRExecWithInternals fields nextScope
      (directInternalHelperCallSourceResult runtime sourceResult)
      (directInternalHelperCallIRResult callerState helper bodyResult)

/-- The remaining direct return-binding helper-call summary obligation after the
source statement reduction and singleton helper-call IR summary bridge have been
applied. -/
abbrev DirectInternalHelperAssignSummaryStepPostcondition
    {runtimeContract : IRContract} {spec : CompilationModel}
    (fields : List Field) (nextScope : List String)
    {calleeName : String}
    (names : List String)
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (helperFuel : Nat)
    (runtime : SourceSemantics.RuntimeState)
    (argVals : List Nat)
    (callerState : IRState)
    (helper : IRInternalFunctionDef)
    (bodyResult : IRExecResultWithInternals) : Prop :=
  let sourceResult :=
    SourceSemantics.interpretInternalFunctionFuel
      spec helperFuel hctx.sourceWitness.callee runtime.world argVals
  hctx.sourceWitness.summary.contract.post helperFuel runtime.world argVals
      sourceResult.success sourceResult.returnValue sourceResult.world →
    stmtStepMatchesIRExecWithInternals fields nextScope
      (directInternalHelperAssignSourceResult runtime names sourceResult)
      (internalHelperAssignCallResult names callerState helper bodyResult)

section DirectInternalHelperStatementSummaryStepMatch

variable {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
variable {scope : List String} {calleeName : String}
variable {args : List Expr} {helper : IRInternalFunctionDef}
variable {runtime : SourceSemantics.RuntimeState}
variable {state callerState : IRState}
variable {argVals : List Nat} {argExprs : List YulExpr}
variable {sourceBindings entryBindings : List (String × Nat)}

/-- Direct void helper-call step match at the exact helper-call fuel required by
`execIRStmtsWithInternals_internalCall_obeys_internal_helper_summary`.

This theorem is the public handoff from the source statement context bridge and
the N1a/N2/N3 IR helper-summary bridge to the final direct-call head-step proof.
The remaining `hpostMatch` argument is intentionally explicit: it is the exact
place where downstream rank-summary evidence must turn the helper summary post
into the concrete source/IR statement-step state relation. -/
theorem directInternalHelperStatementContextBridge_callStepMatch_at_internalHelperCallFuel
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperFuel extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (bodyCtx : InternalHelperBodyExecContext runtimeContract spec
      hctx.sourceWitness.callee helper callerState runtime.world argVals
      sourceBindings entryBindings helperFuel)
    (harity : helper.params.length = hctx.sourceWitness.callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hsourceArgs :
      SourceSemantics.evalExprListWithHelpers spec fields (helperFuel + 1)
        runtime args = some argVals)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract
          (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values argVals callerState)
    (hpostMatch :
      DirectInternalHelperCallSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        hctx helperFuel runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals extraFuel)) :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCall calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields (helperFuel + 1) runtime (Stmt.internalCall calleeName args))
      (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.exprStmt (YulExpr.call
          (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  have hsource :=
    directInternalHelperStatementContextBridge_sourceCallEvidence
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (calleeName := calleeName) (args := args) hctx hnodup
      (fuel := helperFuel) (state := runtime) hsourceArgs
  have hir :=
    execIRStmtsWithInternals_internalCall_obeys_internal_helper_summary
      (runtimeContract := runtimeContract) (spec := spec)
      (callee := hctx.sourceWitness.callee) (helper := helper)
      (state := state) (callerState := callerState)
      (initialWorld := runtime.world) (args := argVals)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      (summary := hctx.sourceWitness.summary.contract)
      helperFuel extraFuel hfuelPos bodyCtx hctx.summarySound harity hfind hirArgs
  rw [hsource.1, hir.1]
  exact hpostMatch hsource.2

/-- Direct return-binding helper-call step match at the exact helper-call fuel
required by
`execIRStmtsWithInternals_internalCallAssign_obeys_internal_helper_summary`. -/
theorem directInternalHelperStatementContextBridge_assignStepMatch_at_internalHelperCallFuel
    {names : List String}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperFuel extraFuel : Nat)
    (hfuelPos : 0 < helperFuel)
    (bodyCtx : InternalHelperBodyExecContext runtimeContract spec
      hctx.sourceWitness.callee helper callerState runtime.world argVals
      sourceBindings entryBindings helperFuel)
    (harity : helper.params.length = hctx.sourceWitness.callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hsourceArgs :
      SourceSemantics.evalExprListWithHelpers spec fields (helperFuel + 1)
        runtime args = some argVals)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract
          (internalHelperCallFuel helper extraFuel + 1) state argExprs =
        .values argVals callerState)
    (hpostMatch :
      DirectInternalHelperAssignSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        names hctx helperFuel runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals extraFuel)) :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields (helperFuel + 1) runtime
        (Stmt.internalCallAssign names calleeName args))
      (execIRStmtsWithInternals runtimeContract
        (internalHelperCallFuel helper extraFuel + 3) state
        [YulStmt.letMany names (YulExpr.call
          (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  have hsource :=
    directInternalHelperStatementContextBridge_sourceAssignEvidence
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (calleeName := calleeName) (names := names) (args := args)
      hctx hnodup (fuel := helperFuel) (state := runtime) hsourceArgs
  have hir :=
    execIRStmtsWithInternals_internalCallAssign_obeys_internal_helper_summary
      (runtimeContract := runtimeContract) (spec := spec)
      (callee := hctx.sourceWitness.callee) (helper := helper)
      (state := state) (callerState := callerState)
      (initialWorld := runtime.world) (names := names) (calleeName := calleeName)
      (argExprs := argExprs) (args := argVals)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      (summary := hctx.sourceWitness.summary.contract)
      helperFuel extraFuel hfuelPos bodyCtx hctx.summarySound harity hfind hirArgs
  rw [hsource.1, hir.1]
  exact hpostMatch hsource.2

noncomputable abbrev directInternalHelperExtraFuel
    (helper : IRInternalFunctionDef) (irFuel : Nat) : Nat :=
  irFuel - (sizeOf helper.body + 2)

section DirectInternalHelperStatementSufficientFuel

variable {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
variable {scope : List String} {calleeName : String}
variable {args : List Expr} {helper : IRInternalFunctionDef}
variable {runtime : SourceSemantics.RuntimeState}
variable {state callerState : IRState}
variable {argVals : List Nat} {argExprs : List YulExpr}
variable {sourceBindings entryBindings : List (String × Nat)}

/-- Re-index the exact-fuel direct void-call bridge under explicit sufficient-fuel bounds. -/
theorem directInternalHelperStatementContextBridge_callStepMatch_of_sufficientFuel
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName) (hnodup : (spec.functions.map (·.name)).Nodup)
    (stmtHelperFuel irFuel : Nat)
    (hstmtFuel : 1 < stmtHelperFuel)
    (hirFuel : sizeOf helper.body + 2 ≤ irFuel)
    (bodyCtx : InternalHelperBodyExecContext runtimeContract spec
      hctx.sourceWitness.callee helper callerState runtime.world argVals
      sourceBindings entryBindings (stmtHelperFuel - 1))
    (harity : helper.params.length = hctx.sourceWitness.callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hsourceArgs : SourceSemantics.evalExprListWithHelpers spec fields stmtHelperFuel runtime args = some argVals)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals callerState)
    (hpostMatch :
      DirectInternalHelperCallSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        hctx (stmtHelperFuel - 1) runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals
          (directInternalHelperExtraFuel helper irFuel))) :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCall calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields stmtHelperFuel runtime
        (Stmt.internalCall calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.exprStmt (YulExpr.call
          (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  have hbodyFuelPos : 0 < stmtHelperFuel - 1 := by omega
  have hstmtFuelEq : stmtHelperFuel - 1 + 1 = stmtHelperFuel := by omega
  have hirFuelEq :
      internalHelperCallFuel helper (directInternalHelperExtraFuel helper irFuel) = irFuel := by
    unfold internalHelperCallFuel
    unfold directInternalHelperExtraFuel
    omega
  rw [← hstmtFuelEq] at hsourceArgs
  rw [← hirFuelEq] at hirArgs ⊢
  have hmatch :=
    directInternalHelperStatementContextBridge_callStepMatch_at_internalHelperCallFuel
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (args := args)
      (helper := helper) (runtime := runtime) (state := state)
      (callerState := callerState) (argVals := argVals) (argExprs := argExprs)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      hctx hnodup (stmtHelperFuel - 1) (directInternalHelperExtraFuel helper irFuel)
      hbodyFuelPos bodyCtx harity hfind hsourceArgs hirArgs hpostMatch
  simpa [hstmtFuelEq] using hmatch

/-- Return-binding counterpart of the sufficient-fuel direct void-call adapter. -/
theorem directInternalHelperStatementContextBridge_assignStepMatch_of_sufficientFuel
    {names : List String}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName) (hnodup : (spec.functions.map (·.name)).Nodup)
    (stmtHelperFuel irFuel : Nat)
    (hstmtFuel : 1 < stmtHelperFuel)
    (hirFuel : sizeOf helper.body + 2 ≤ irFuel)
    (bodyCtx : InternalHelperBodyExecContext runtimeContract spec
      hctx.sourceWitness.callee helper callerState runtime.world argVals
      sourceBindings entryBindings (stmtHelperFuel - 1))
    (harity : helper.params.length = hctx.sourceWitness.callee.params.length)
    (hfind : findInternalFunction? runtimeContract
      (CompilationModel.internalFunctionYulName calleeName) = some helper)
    (hsourceArgs : SourceSemantics.evalExprListWithHelpers spec fields stmtHelperFuel runtime args = some argVals)
    (hirArgs :
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals callerState)
    (hpostMatch :
      DirectInternalHelperAssignSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        names hctx (stmtHelperFuel - 1) runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals
          (directInternalHelperExtraFuel helper irFuel))) :
    stmtStepMatchesIRExecWithInternals fields
      (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
      (SourceSemantics.execStmtWithHelpers spec fields stmtHelperFuel runtime
        (Stmt.internalCallAssign names calleeName args))
      (execIRStmtsWithInternals runtimeContract (irFuel + 3) state
        [YulStmt.letMany names (YulExpr.call
          (CompilationModel.internalFunctionYulName calleeName) argExprs)]) := by
  have hbodyFuelPos : 0 < stmtHelperFuel - 1 := by omega
  have hstmtFuelEq : stmtHelperFuel - 1 + 1 = stmtHelperFuel := by omega
  have hirFuelEq :
      internalHelperCallFuel helper (directInternalHelperExtraFuel helper irFuel) = irFuel := by
    unfold internalHelperCallFuel
    unfold directInternalHelperExtraFuel
    omega
  rw [← hstmtFuelEq] at hsourceArgs
  rw [← hirFuelEq] at hirArgs ⊢
  have hmatch :=
    directInternalHelperStatementContextBridge_assignStepMatch_at_internalHelperCallFuel
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (names := names) (args := args)
      (helper := helper) (runtime := runtime) (state := state)
      (callerState := callerState) (argVals := argVals) (argExprs := argExprs)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      hctx hnodup (stmtHelperFuel - 1) (directInternalHelperExtraFuel helper irFuel)
      hbodyFuelPos bodyCtx harity hfind hsourceArgs hirArgs hpostMatch
  simpa [hstmtFuelEq] using hmatch

end DirectInternalHelperStatementSufficientFuel

section DirectInternalHelperFuelSplitConsumer

variable {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
variable {scope : List String} {calleeName : String}
variable {args : List Expr} {argExprs : List YulExpr}
variable {runtime : SourceSemantics.RuntimeState} {state : IRState}

abbrev DirectInternalHelperCallSufficientFuelEvidence
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (helperBodySize stmtHelperFuel irFuel : Nat)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) : Prop :=
  ∃ (helper : IRInternalFunctionDef) (callerState : IRState) (argVals : List Nat)
      (sourceBindings entryBindings : List (String × Nat)),
    sizeOf helper.body = helperBodySize ∧
      InternalHelperBodyExecContext runtimeContract spec
        hctx.sourceWitness.callee helper callerState runtime.world argVals
        sourceBindings entryBindings (stmtHelperFuel - 1) ∧
      helper.params.length = hctx.sourceWitness.callee.params.length ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      SourceSemantics.evalExprListWithHelpers spec fields stmtHelperFuel runtime args =
        some argVals ∧
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals callerState ∧
      DirectInternalHelperCallSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCall calleeName args))
        hctx (stmtHelperFuel - 1) runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals
          (directInternalHelperExtraFuel helper irFuel))

/-- Consume the direct-call sufficient-fuel statement-context adapter as the
normal-region bridge required by the fuel-split singleton constructor. -/
theorem internalCallWithInternalsSufficientBridge_of_directContextEvidence
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperBodySize : Nat)
    (hevidence :
      ∀ runtime state stmtHelperFuel irFuel,
        1 < stmtHelperFuel →
        helperBodySize + 2 ≤ irFuel →
        DirectInternalHelperCallSufficientFuelEvidence
          (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
          (scope := scope) (calleeName := calleeName) (args := args)
          (argExprs := argExprs) hctx helperBodySize stmtHelperFuel irFuel runtime state) :
    InternalCallWithInternalsSufficientBridge runtimeContract spec fields scope
      calleeName args argExprs helperBodySize := by
  intro runtime state stmtHelperFuel irFuel hstmtFuel hirFuel hfuel hexact hscope hbounded hruntime
  rcases hevidence runtime state stmtHelperFuel irFuel hstmtFuel hirFuel with
    ⟨helper, callerState, argVals, sourceBindings, entryBindings, hsize, bodyCtx,
      harity, hfind, hsourceArgs, hirArgs, hpostMatch⟩
  have hirFuel' : sizeOf helper.body + 2 ≤ irFuel := by omega
  exact
    directInternalHelperStatementContextBridge_callStepMatch_of_sufficientFuel
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (args := args)
      (helper := helper) (runtime := runtime) (state := state)
      (callerState := callerState) (argVals := argVals) (argExprs := argExprs)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      hctx hnodup stmtHelperFuel irFuel hstmtFuel hirFuel' bodyCtx harity hfind
      hsourceArgs hirArgs hpostMatch

/-- Direct void-call singleton proof from the reviewed fuel split: the normal
region is discharged by direct statement-context evidence, while the residual
low/insufficient-fuel branch remains an explicit caller obligation. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_directContextFuelSplit
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperBodySize : Nat)
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCall calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (hevidence :
      ∀ runtime state stmtHelperFuel irFuel,
        1 < stmtHelperFuel →
        helperBodySize + 2 ≤ irFuel →
        DirectInternalHelperCallSufficientFuelEvidence
          (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
          (scope := scope) (calleeName := calleeName) (args := args)
          (argExprs := argExprs) hctx helperBodySize stmtHelperFuel irFuel runtime state)
    (hresidual :
      InternalCallWithInternalsResidualBridge runtimeContract spec fields scope
        calleeName args argExprs helperBodySize) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals runtimeContract spec fields scope
      (Stmt.internalCall calleeName args) compiledIR := by
  exact
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_fuelSplitBridge
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (args := args)
      (compiledIR := compiledIR) (argExprs := argExprs) helperBodySize
      hcompile hargCompile
      (internalCallWithInternalsSufficientBridge_of_directContextEvidence
        (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
        (scope := scope) (calleeName := calleeName) (args := args)
        (argExprs := argExprs) hctx hnodup helperBodySize hevidence)
      hresidual

abbrev DirectInternalHelperAssignSufficientFuelEvidence
    (names : List String)
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (helperBodySize stmtHelperFuel irFuel : Nat)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) : Prop :=
  ∃ (helper : IRInternalFunctionDef) (callerState : IRState) (argVals : List Nat)
      (sourceBindings entryBindings : List (String × Nat)),
    sizeOf helper.body = helperBodySize ∧
      InternalHelperBodyExecContext runtimeContract spec
        hctx.sourceWitness.callee helper callerState runtime.world argVals
        sourceBindings entryBindings (stmtHelperFuel - 1) ∧
      helper.params.length = hctx.sourceWitness.callee.params.length ∧
      findInternalFunction? runtimeContract
        (CompilationModel.internalFunctionYulName calleeName) = some helper ∧
      SourceSemantics.evalExprListWithHelpers spec fields stmtHelperFuel runtime args =
        some argVals ∧
      evalIRExprsWithInternals runtimeContract (irFuel + 1) state argExprs =
        .values argVals callerState ∧
      DirectInternalHelperAssignSummaryStepPostcondition fields
        (stmtNextScope scope (Stmt.internalCallAssign names calleeName args))
        names hctx (stmtHelperFuel - 1) runtime argVals callerState helper
        (internalHelperBodyIRExec runtimeContract helper callerState argVals
          (directInternalHelperExtraFuel helper irFuel))

/-- Assignment-call counterpart of
`internalCallWithInternalsSufficientBridge_of_directContextEvidence`. -/
theorem internalCallAssignWithInternalsSufficientBridge_of_directContextEvidence
    {names : List String}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperBodySize : Nat)
    (hevidence :
      ∀ runtime state stmtHelperFuel irFuel,
        1 < stmtHelperFuel →
        helperBodySize + 2 ≤ irFuel →
        DirectInternalHelperAssignSufficientFuelEvidence
          (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
          (scope := scope) (calleeName := calleeName) (args := args)
          (argExprs := argExprs) names hctx helperBodySize stmtHelperFuel irFuel runtime state) :
    InternalCallAssignWithInternalsSufficientBridge runtimeContract spec fields scope
      names calleeName args argExprs helperBodySize := by
  intro runtime state stmtHelperFuel irFuel hstmtFuel hirFuel hfuel hexact hscope hbounded hruntime
  rcases hevidence runtime state stmtHelperFuel irFuel hstmtFuel hirFuel with
    ⟨helper, callerState, argVals, sourceBindings, entryBindings, hsize, bodyCtx,
      harity, hfind, hsourceArgs, hirArgs, hpostMatch⟩
  have hirFuel' : sizeOf helper.body + 2 ≤ irFuel := by omega
  exact
    directInternalHelperStatementContextBridge_assignStepMatch_of_sufficientFuel
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (calleeName := calleeName) (names := names) (args := args)
      (helper := helper) (runtime := runtime) (state := state)
      (callerState := callerState) (argVals := argVals) (argExprs := argExprs)
      (sourceBindings := sourceBindings) (entryBindings := entryBindings)
      hctx hnodup stmtHelperFuel irFuel hstmtFuel hirFuel' bodyCtx harity hfind
      hsourceArgs hirArgs hpostMatch

/-- Assignment-call singleton counterpart of
`compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCall_of_directContextFuelSplit`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_directContextFuelSplit
    {names : List String}
    (hctx : DirectInternalHelperStatementContextBridge runtimeContract spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (helperBodySize : Nat)
    {compiledIR : List YulStmt}
    (hcompile :
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        (Stmt.internalCallAssign names calleeName args) spec.functions = Except.ok compiledIR)
    (hargCompile :
      CompilationModel.compileInternalCallArgs fields .calldata spec.functions
        calleeName args = Except.ok argExprs)
    (hevidence :
      ∀ runtime state stmtHelperFuel irFuel,
        1 < stmtHelperFuel →
        helperBodySize + 2 ≤ irFuel →
        DirectInternalHelperAssignSufficientFuelEvidence
          (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
          (scope := scope) (calleeName := calleeName) (args := args)
          (argExprs := argExprs) names hctx helperBodySize stmtHelperFuel irFuel runtime state)
    (hresidual :
      InternalCallAssignWithInternalsResidualBridge runtimeContract spec fields scope names
        calleeName args argExprs helperBodySize) :
    CompiledStmtStepWithHelpersAndHelperIRWithInternals runtimeContract spec fields scope
      (Stmt.internalCallAssign names calleeName args) compiledIR := by
  exact
    compiledStmtStepWithHelpersAndHelperIRWithInternals_internalCallAssign_of_fuelSplitBridge
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (scope := scope) (names := names) (calleeName := calleeName) (args := args)
      (compiledIR := compiledIR) (argExprs := argExprs) helperBodySize
      hcompile hargCompile
      (internalCallAssignWithInternalsSufficientBridge_of_directContextEvidence
        (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
        (scope := scope) (calleeName := calleeName) (args := args)
        (argExprs := argExprs) (names := names) hctx hnodup helperBodySize hevidence)
      hresidual

end DirectInternalHelperFuelSplitConsumer

end DirectInternalHelperStatementSummaryStepMatch

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

/-- Post-expression state facts paired with the compositional helper payload.

The base helper-head payload intentionally stays smaller: proving these facts
for a direct `Expr.internalCall` still needs a compiled-helper state-preservation
theorem for `execIRInternalFunctionWithInternals`.  This companion is the narrow
shape statement-head adapters need once a constructor-specific expression proof
has already established that the final IR state still matches the unchanged
source runtime and old scope bindings. -/
def ExprInternalHelperCompositionalPostStateResult
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (expr : Expr)
    (exprIR : YulExpr)
    (helperFuel irFuel : Nat)
    (runtime headRuntime : SourceSemantics.RuntimeState)
    (state headState finalState : IRState)
    (value : Nat) : Prop :=
  ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      expr exprIR helperFuel irFuel runtime headRuntime state headState
      finalState value ∧
    FunctionBody.runtimeStateMatchesIR fields runtime finalState ∧
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState ∧
    value < Compiler.Constants.evmModulus

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

theorem exprInternalHelperCompositionalContextResult_of_outer_facts
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {headExpr expr : Expr} {headExprIR exprIR : YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {state headState headFinalState finalState : IRState}
    {headValue value : Nat}
    (hhead :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        headExpr headExprIR helperFuel irFuel runtime headRuntime state headState
        headFinalState headValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions expr =
        Except.ok exprIR)
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime expr =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) state exprIR =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      expr exprIR helperFuel irFuel runtime headRuntime state headState finalState value := by
  -- Blocker: a fully automatic theorem over every non-call `Expr` constructor
  -- still needs a uniform helper-aware source/IR expression compiler lemma,
  -- including sequential IR state threading for sibling expressions.
  unfold ExprInternalHelperCompositionalContextResult at hhead ⊢
  rcases hhead with ⟨_, _, _, hmatches, hpayload⟩
  exact ⟨hcompile, hsource, hir, hmatches, hpayload⟩

/-- Variant of `exprInternalHelperCompositionalContextResult_of_outer_facts`
where the helper-head IR expression starts from an intermediate state rather
than the parent expression's entry state.  This is the shape needed for
right-hand siblings: the left sibling may have already advanced IR state before
the helper-bearing right expression is evaluated, while source expression
evaluation still uses the same source runtime. -/
theorem exprInternalHelperCompositionalContextResult_of_outer_facts_threaded_head
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {headExpr expr : Expr} {headExprIR exprIR : YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headEntryState headState headFinalState finalState : IRState}
    {headValue value : Nat}
    (hhead :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        headExpr headExprIR helperFuel irFuel runtime headRuntime headEntryState
        headState headFinalState headValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions expr =
        Except.ok exprIR)
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime expr =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState exprIR =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      expr exprIR helperFuel irFuel runtime headRuntime parentState headState
      finalState value := by
  unfold ExprInternalHelperCompositionalContextResult at hhead ⊢
  rcases hhead with ⟨_, _, _, hmatches, hpayload⟩
  exact ⟨hcompile, hsource, hir, hmatches, hpayload⟩

/-- Unary non-call expression-context lift.  This is the common shape for
constructors such as `bitNot`, `logicalNot`, `mload`, `tload`, `calldataload`,
and single-child dynamic-array helpers once their outer facts are proved. -/
theorem exprInternalHelperCompositionalContextResult_unary_context
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {child : Expr} {childIR : YulExpr}
    {mkExpr : Expr → Expr} {mkIR : YulExpr → YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {state headState childFinalState finalState : IRState}
    {childValue value : Nat}
    (hchild :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        child childIR helperFuel irFuel runtime headRuntime state headState
        childFinalState childValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (mkExpr child) =
        Except.ok (mkIR childIR))
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
          (mkExpr child) =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) state (mkIR childIR) =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (mkExpr child) (mkIR childIR) helperFuel irFuel runtime headRuntime state
      headState finalState value := by
  exact
    exprInternalHelperCompositionalContextResult_of_outer_facts
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (headExpr := child) (headExprIR := childIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := state) (headState := headState)
      hchild hcompile hsource hir

/-- Binary non-call expression-context lift when the helper payload is in the
left child.  Sibling evaluation state threading is intentionally part of the
outer `hir` fact supplied by the caller. -/
theorem exprInternalHelperCompositionalContextResult_binary_left_context
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr}
    {mkExpr : Expr → Expr → Expr} {mkIR : YulExpr → YulExpr → YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {state headState leftFinalState finalState : IRState}
    {leftValue value : Nat}
    (hleft :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        left leftIR helperFuel irFuel runtime headRuntime state headState
        leftFinalState leftValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (mkExpr left right) =
        Except.ok (mkIR leftIR rightIR))
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
          (mkExpr left right) =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) state
          (mkIR leftIR rightIR) =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (mkExpr left right) (mkIR leftIR rightIR) helperFuel irFuel runtime
      headRuntime state headState finalState value := by
  exact
    exprInternalHelperCompositionalContextResult_of_outer_facts
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (headExpr := left) (headExprIR := leftIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := state) (headState := headState)
      hleft hcompile hsource hir

/-- Binary non-call expression-context lift when the helper payload is in the
right child.  This preserves the helper head while the caller supplies the
already-established outer facts for the whole parent expression. -/
theorem exprInternalHelperCompositionalContextResult_binary_right_context
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr}
    {mkExpr : Expr → Expr → Expr} {mkIR : YulExpr → YulExpr → YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {state headState rightFinalState finalState : IRState}
    {rightValue value : Nat}
    (hright :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        right rightIR helperFuel irFuel runtime headRuntime state headState
        rightFinalState rightValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (mkExpr left right) =
        Except.ok (mkIR leftIR rightIR))
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
          (mkExpr left right) =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) state
          (mkIR leftIR rightIR) =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (mkExpr left right) (mkIR leftIR rightIR) helperFuel irFuel runtime
      headRuntime state headState finalState value := by
  exact
    exprInternalHelperCompositionalContextResult_of_outer_facts
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (headExpr := right) (headExprIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := state) (headState := headState)
      hright hcompile hsource hir

/-- Binary non-call expression-context lift when the helper payload is in the
right child and the left sibling has already advanced the IR state.  This is the
threaded counterpart of `exprInternalHelperCompositionalContextResult_binary_right_context`
and is the reusable shape for source/IR expression compiler lemmas over sibling
constructors. -/
theorem exprInternalHelperCompositionalContextResult_binary_right_threaded_context
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr}
    {mkExpr : Expr → Expr → Expr} {mkIR : YulExpr → YulExpr → YulExpr}
    {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {rightValue value : Nat}
    (hright :
      ExprInternalHelperCompositionalContextResult runtimeContract spec fields
        right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
        rightFinalState rightValue)
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (mkExpr left right) =
        Except.ok (mkIR leftIR rightIR))
    (hsource :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime
          (mkExpr left right) =
        some value)
    (hir :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState
          (mkIR leftIR rightIR) =
        .value value finalState) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (mkExpr left right) (mkIR leftIR rightIR) helperFuel irFuel runtime
      headRuntime parentState headState finalState value := by
  exact
    exprInternalHelperCompositionalContextResult_of_outer_facts_threaded_head
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (headExpr := right) (headExprIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (headEntryState := rightEntryState)
      (headState := headState)
      hright hcompile hsource hir

/-- Successful two-argument IR expression evaluation with explicit
left-to-right state threading. -/
theorem evalIRExprsWithInternals_pair_of_values
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state leftState finalState : IRState)
    (leftIR rightIR : YulExpr)
    (leftValue rightValue : Nat)
    (hleft :
      evalIRExprWithInternals runtimeContract fuel state leftIR =
        .value leftValue leftState)
    (hright :
      evalIRExprWithInternals runtimeContract fuel leftState rightIR =
        .value rightValue finalState) :
    evalIRExprsWithInternals runtimeContract fuel state [leftIR, rightIR] =
      .values [leftValue, rightValue] finalState := by
  simp [evalIRExprsWithInternals, hleft, hright]

/-- Helper-aware compiled IR evaluation for a pure two-argument Yul builtin,
with the sibling state threading exposed by
`evalIRExprsWithInternals_pair_of_values`.  Constructor-specific source/compile
lemmas can use this to discharge the IR side for binary non-call expression
contexts after proving the source value computes to the same builtin result. -/
theorem evalIRExprWithInternals_binary_builtin_of_values
    (runtimeContract : IRContract)
    (fuel : Nat)
    (state leftState finalState : IRState)
    (func : String)
    (leftIR rightIR : YulExpr)
    (leftValue rightValue value : Nat)
    (hleft :
      evalIRExprWithInternals runtimeContract fuel state leftIR =
        .value leftValue leftState)
    (hright :
      evalIRExprWithInternals runtimeContract fuel leftState rightIR =
        .value rightValue finalState)
    (hfind : findInternalFunction? runtimeContract func = none)
    (hnotTload : func ≠ "tload")
    (hnotMload : func ≠ "mload")
    (hnotKeccak : func ≠ "keccak256")
    (hbuiltin :
      Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext
          finalState.storage finalState.sender finalState.msgValue finalState.thisAddress
          finalState.blockTimestamp finalState.blockNumber finalState.chainId
          finalState.blobBaseFee finalState.txOrigin finalState.selector
          finalState.calldata func [leftValue, rightValue] =
        some value) :
    evalIRExprWithInternals runtimeContract fuel state
        (YulExpr.call func [leftIR, rightIR]) =
      .value value finalState := by
  have hargs :
      evalIRExprsWithInternals runtimeContract fuel state [leftIR, rightIR] =
        .values [leftValue, rightValue] finalState :=
    evalIRExprsWithInternals_pair_of_values runtimeContract fuel state leftState finalState
      leftIR rightIR leftValue rightValue hleft hright
  simp [evalIRExprWithInternals_call,
    evalIRCallWithInternals_of_builtin runtimeContract fuel state func
      [leftIR, rightIR] [leftValue, rightValue] finalState hargs hfind
      hnotTload hnotMload hnotKeccak,
    hbuiltin]

/-- `Nat` values coerced to `Uint256` may be normalized before or after the
coercion when using the EVM modulus. -/
theorem uint256_ofNat_evmModulus_mod (value : Nat) :
    Verity.Core.Uint256.ofNat value =
      Verity.Core.Uint256.ofNat (value % Compiler.Constants.evmModulus) := by
  ext
  simp [Verity.Core.Uint256.ofNat, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus]

/-- Shared source/Yul value for the `Expr.add` constructor. -/
def exprAddValue (leftValue rightValue : Nat) : Nat :=
  (Verity.Core.Uint256.add
    (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
    (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).val

theorem exprAddValue_lt_evmModulus (leftValue rightValue : Nat) :
    exprAddValue leftValue rightValue < Compiler.Constants.evmModulus := by
  simpa [exprAddValue, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus] using
    (Verity.Core.Uint256.add
      (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).isLt

/-- Constructor-specific compiler shape for `Expr.add` once both children have
already compiled. -/
theorem compileExprWithInternals_add_of_children
    {fields : List Field} {internalFunctions : List FunctionSpec}
    {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions right =
        Except.ok rightIR) :
    CompilationModel.compileExprWithInternals fields .calldata internalFunctions
        (Expr.add left right) =
      Except.ok (YulExpr.call "add" [leftIR, rightIR]) := by
  simp only [CompilationModel.compileExprWithInternals, hcompileLeft, hcompileRight,
    CompilationModel.yulBinOp]
  rfl

/-- Constructor-specific source semantics for `Expr.add` once both child source
values are known. -/
theorem evalExprWithHelpers_add_of_values
    (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (runtime : SourceSemantics.RuntimeState)
    {left right : Expr} {leftValue rightValue : Nat}
    (hsourceLeft :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime left =
        some leftValue)
    (hsourceRight :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime right =
        some rightValue) :
    SourceSemantics.evalExprWithHelpers spec fields fuel runtime (Expr.add left right) =
      some (exprAddValue leftValue rightValue) := by
  simp [SourceSemantics.evalExprWithHelpers, hsourceLeft, hsourceRight,
    exprAddValue, Verity.Core.Uint256.add]
  conv_lhs =>
    rw [uint256_ofNat_evmModulus_mod leftValue,
      uint256_ofNat_evmModulus_mod rightValue]

/-- Constructor-specific builtin semantics for the compiled Yul `add` call. -/
theorem evalBuiltinCallWithEvmYulLeanContext_add_of_values
    (state : IRState) (leftValue rightValue : Nat) :
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext
        state.storage state.sender state.msgValue state.thisAddress
        state.blockTimestamp state.blockNumber state.chainId state.blobBaseFee
        state.txOrigin state.selector state.calldata "add" [leftValue, rightValue] =
      some (exprAddValue leftValue rightValue) := by
  simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    exprAddValue, Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Compiler.Constants.evmModulus, Nat.add_mod]

/-- Constructor-specific right-child bridge for `Expr.add`.

This is the first non-call expression constructor that discharges its own
source, compile, and IR facts using the threaded binary API.  The left operand
is evaluated first in IR and may advance the state; the helper-bearing right
operand is then evaluated from that intermediate state, while source evaluation
continues from the original runtime. -/
theorem exprInternalHelperCompositionalContextResult_add_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime left =
      some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindAdd : findInternalFunction? runtimeContract "add" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields (Expr.add left right)
      (YulExpr.call "add" [leftIR, rightIR]) helperFuel irFuel runtime headRuntime
      parentState headState finalState (exprAddValue leftValue rightValue) := by
  let value := exprAddValue leftValue rightValue
  have hrightFacts := hright
  unfold ExprInternalHelperCompositionalContextResult at hrightFacts
  rcases hrightFacts with ⟨hcompileRight, hsourceRight, _, _, _⟩
  let hcompile := compileExprWithInternals_add_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_add_of_values spec fields (helperFuel + 1) runtime
    hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_add_of_values finalState leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState rightEntryState finalState "add" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindAdd (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_right_threaded_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.add) (mkIR := fun a b => YulExpr.call "add" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hright hcompile hsource hir

/-- Post-state companion for the phase-9 `Expr.add` right-helper bridge.

The `Expr.add` IR evaluation finishes in the same state produced by the
right-hand child, so once the right child carries the post-expression source/IR
state facts, the parent expression preserves them without any additional
helper-body theorem. -/
theorem exprInternalHelperCompositionalPostStateResult_add_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
      rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime left =
      some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindAdd : findInternalFunction? runtimeContract "add" = none)
    (hfinalEq : finalState = rightFinalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.add left right) (YulExpr.call "add" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprAddValue leftValue rightValue) := by
  rcases hright with ⟨hrightResult, hrightRuntime, hrightExact, _hrightLt⟩
  subst hfinalEq
  refine ⟨?_, hrightRuntime, hrightExact, exprAddValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_add_right_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hrightResult hcompileLeft hsourceLeft hirLeft hirRight hfindAdd

/-- Constructor-specific left-child bridge for `Expr.add`.

The helper-bearing left operand evaluates first; the right operand is then
evaluated from the left operand's final IR state. -/
theorem exprInternalHelperCompositionalContextResult_add_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime right =
        some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindAdd : findInternalFunction? runtimeContract "add" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.add left right) (YulExpr.call "add" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprAddValue leftValue rightValue) := by
  let value := exprAddValue leftValue rightValue
  have hleftFacts := hleft
  unfold ExprInternalHelperCompositionalContextResult at hleftFacts
  rcases hleftFacts with ⟨hcompileLeft, hsourceLeft, hirLeft, _, _⟩
  let hcompile := compileExprWithInternals_add_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_add_of_values spec fields (helperFuel + 1)
    runtime hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_add_of_values finalState
    leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState leftFinalState finalState "add" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindAdd (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_left_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.add) (mkIR := fun a b => YulExpr.call "add" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := parentState) (headState := headState)
      hleft hcompile hsource hir

/-- Post-state companion for the `Expr.add` left-helper bridge. -/
theorem exprInternalHelperCompositionalPostStateResult_add_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight :
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1) runtime right =
        some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindAdd : findInternalFunction? runtimeContract "add" = none)
    (hfinalRuntime : FunctionBody.runtimeStateMatchesIR fields runtime finalState)
    (hfinalExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.add left right) (YulExpr.call "add" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprAddValue leftValue rightValue) := by
  rcases hleft with ⟨hleftResult, _, _, _⟩
  refine ⟨?_, hfinalRuntime, hfinalExact, exprAddValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_add_left_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (headState := headState)
      hleftResult hcompileRight hsourceRight hirRight hfindAdd

/-- Shared source/Yul value for the `Expr.mul` constructor. -/
def exprMulValue (leftValue rightValue : Nat) : Nat :=
  (Verity.Core.Uint256.mul
    (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
    (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).val

theorem exprMulValue_lt_evmModulus (leftValue rightValue : Nat) :
    exprMulValue leftValue rightValue < Compiler.Constants.evmModulus := by
  simpa [exprMulValue, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus] using
    (Verity.Core.Uint256.mul
      (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).isLt

theorem compileExprWithInternals_mul_of_children
    {fields : List Field} {internalFunctions : List FunctionSpec}
    {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions right =
        Except.ok rightIR) :
    CompilationModel.compileExprWithInternals fields .calldata internalFunctions
        (Expr.mul left right) =
      Except.ok (YulExpr.call "mul" [leftIR, rightIR]) := by
  simp only [CompilationModel.compileExprWithInternals, hcompileLeft, hcompileRight,
    CompilationModel.yulBinOp]
  rfl

theorem evalExprWithHelpers_mul_of_values
    (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (runtime : SourceSemantics.RuntimeState)
    {left right : Expr} {leftValue rightValue : Nat}
    (hsourceLeft :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime left =
        some leftValue)
    (hsourceRight :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime right =
        some rightValue) :
    SourceSemantics.evalExprWithHelpers spec fields fuel runtime (Expr.mul left right) =
      some (exprMulValue leftValue rightValue) := by
  simp [SourceSemantics.evalExprWithHelpers, hsourceLeft, hsourceRight,
    exprMulValue, Verity.Core.Uint256.mul]
  conv_lhs =>
    rw [uint256_ofNat_evmModulus_mod leftValue,
      uint256_ofNat_evmModulus_mod rightValue]
  change
    (Verity.Core.Uint256.mul
      (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).val =
    leftValue * rightValue % Compiler.Constants.evmModulus
  simp only [Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat]
  simp [Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Compiler.Constants.evmModulus, Nat.mul_mod]

theorem evalBuiltinCallWithEvmYulLeanContext_mul_of_values
    (state : IRState) (leftValue rightValue : Nat) :
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext
        state.storage state.sender state.msgValue state.thisAddress
        state.blockTimestamp state.blockNumber state.chainId state.blobBaseFee
        state.txOrigin state.selector state.calldata "mul" [leftValue, rightValue] =
      some (exprMulValue leftValue rightValue) := by
  simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    exprMulValue, Verity.Core.Uint256.mul, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Compiler.Constants.evmModulus, Nat.mul_mod]

theorem exprInternalHelperCompositionalContextResult_mul_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
      rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime left = some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindMul : findInternalFunction? runtimeContract "mul" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.mul left right) (YulExpr.call "mul" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprMulValue leftValue rightValue) := by
  let value := exprMulValue leftValue rightValue
  have hrightFacts := hright
  unfold ExprInternalHelperCompositionalContextResult at hrightFacts
  rcases hrightFacts with ⟨hcompileRight, hsourceRight, _, _, _⟩
  let hcompile := compileExprWithInternals_mul_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_mul_of_values spec fields (helperFuel + 1) runtime
    hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_mul_of_values finalState leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState rightEntryState finalState "mul" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindMul (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_right_threaded_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.mul) (mkIR := fun a b => YulExpr.call "mul" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hright hcompile hsource hir

theorem exprInternalHelperCompositionalPostStateResult_mul_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
      rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime left = some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindMul : findInternalFunction? runtimeContract "mul" = none)
    (hfinalEq : finalState = rightFinalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.mul left right) (YulExpr.call "mul" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprMulValue leftValue rightValue) := by
  rcases hright with ⟨hrightResult, hrightRuntime, hrightExact, _hrightLt⟩
  subst hfinalEq
  refine ⟨?_, hrightRuntime, hrightExact, exprMulValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_mul_right_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hrightResult hcompileLeft hsourceLeft hirLeft hirRight hfindMul

theorem exprInternalHelperCompositionalContextResult_mul_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime right = some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindMul : findInternalFunction? runtimeContract "mul" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.mul left right) (YulExpr.call "mul" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprMulValue leftValue rightValue) := by
  let value := exprMulValue leftValue rightValue
  have hleftFacts := hleft
  unfold ExprInternalHelperCompositionalContextResult at hleftFacts
  rcases hleftFacts with ⟨hcompileLeft, hsourceLeft, hirLeft, _, _⟩
  let hcompile := compileExprWithInternals_mul_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_mul_of_values spec fields (helperFuel + 1)
    runtime hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_mul_of_values finalState
    leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState leftFinalState finalState "mul" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindMul (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_left_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.mul) (mkIR := fun a b => YulExpr.call "mul" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := parentState) (headState := headState)
      hleft hcompile hsource hir

theorem exprInternalHelperCompositionalPostStateResult_mul_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime right = some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindMul : findInternalFunction? runtimeContract "mul" = none)
    (hfinalRuntime : FunctionBody.runtimeStateMatchesIR fields runtime finalState)
    (hfinalExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.mul left right) (YulExpr.call "mul" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprMulValue leftValue rightValue) := by
  rcases hleft with ⟨hleftResult, _, _, _⟩
  refine ⟨?_, hfinalRuntime, hfinalExact, exprMulValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_mul_left_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (headState := headState)
      hleftResult hcompileRight hsourceRight hirRight hfindMul

/-- Shared source/Yul value for the `Expr.sub` constructor. -/
def exprSubValue (leftValue rightValue : Nat) : Nat :=
  (Verity.Core.Uint256.sub
    (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
    (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).val

theorem exprSubValue_lt_evmModulus (leftValue rightValue : Nat) :
    exprSubValue leftValue rightValue < Compiler.Constants.evmModulus := by
  simpa [exprSubValue, Verity.Core.Uint256.modulus,
    Verity.Core.UINT256_MODULUS, Compiler.Constants.evmModulus] using
    (Verity.Core.Uint256.sub
      (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).isLt

theorem exprSubValue_eq_builtin (leftValue rightValue : Nat) :
    exprSubValue leftValue rightValue =
      (Compiler.Constants.evmModulus + (leftValue % Compiler.Constants.evmModulus) -
        (rightValue % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus := by
  exact FunctionBody.uint256_sub_val_eq
    (Nat.mod_lt leftValue (by decide : 0 < Compiler.Constants.evmModulus))
    (Nat.mod_lt rightValue (by decide : 0 < Compiler.Constants.evmModulus))

theorem compileExprWithInternals_sub_of_children
    {fields : List Field} {internalFunctions : List FunctionSpec}
    {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions right =
        Except.ok rightIR) :
    CompilationModel.compileExprWithInternals fields .calldata internalFunctions
        (Expr.sub left right) =
      Except.ok (YulExpr.call "sub" [leftIR, rightIR]) := by
  simp only [CompilationModel.compileExprWithInternals, hcompileLeft, hcompileRight,
    CompilationModel.yulBinOp]
  rfl

theorem evalExprWithHelpers_sub_of_values
    (spec : CompilationModel) (fields : List Field)
    (fuel : Nat) (runtime : SourceSemantics.RuntimeState)
    {left right : Expr} {leftValue rightValue : Nat}
    (hsourceLeft :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime left =
        some leftValue)
    (hsourceRight :
      SourceSemantics.evalExprWithHelpers spec fields fuel runtime right =
        some rightValue) :
    SourceSemantics.evalExprWithHelpers spec fields fuel runtime (Expr.sub left right) =
      some (exprSubValue leftValue rightValue) := by
  simp [SourceSemantics.evalExprWithHelpers, hsourceLeft, hsourceRight,
    exprSubValue, Verity.Core.Uint256.sub]
  conv_lhs =>
    rw [uint256_ofNat_evmModulus_mod leftValue,
      uint256_ofNat_evmModulus_mod rightValue]
  change
    (Verity.Core.Uint256.sub
      (Verity.Core.Uint256.ofNat (leftValue % Compiler.Constants.evmModulus))
      (Verity.Core.Uint256.ofNat (rightValue % Compiler.Constants.evmModulus))).val =
    if rightValue % Compiler.Constants.evmModulus ≤
        leftValue % Compiler.Constants.evmModulus then
      (leftValue % Compiler.Constants.evmModulus -
          rightValue % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus
    else
      (Compiler.Constants.evmModulus -
          (rightValue % Compiler.Constants.evmModulus -
            leftValue % Compiler.Constants.evmModulus)) % Compiler.Constants.evmModulus
  simp [Verity.Core.Uint256.sub, Verity.Core.Uint256.ofNat,
    Verity.Core.Uint256.modulus, Verity.Core.UINT256_MODULUS,
    Compiler.Constants.evmModulus]

theorem evalBuiltinCallWithEvmYulLeanContext_sub_of_values
    (state : IRState) (leftValue rightValue : Nat) :
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext
        state.storage state.sender state.msgValue state.thisAddress
        state.blockTimestamp state.blockNumber state.chainId state.blobBaseFee
        state.txOrigin state.selector state.calldata "sub" [leftValue, rightValue] =
      some (exprSubValue leftValue rightValue) := by
  rw [exprSubValue_eq_builtin]
  simp [Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext]

theorem exprInternalHelperCompositionalContextResult_sub_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
      rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime left = some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindSub : findInternalFunction? runtimeContract "sub" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.sub left right) (YulExpr.call "sub" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprSubValue leftValue rightValue) := by
  let value := exprSubValue leftValue rightValue
  have hrightFacts := hright
  unfold ExprInternalHelperCompositionalContextResult at hrightFacts
  rcases hrightFacts with ⟨hcompileRight, hsourceRight, _, _, _⟩
  let hcompile := compileExprWithInternals_sub_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_sub_of_values spec fields (helperFuel + 1) runtime
    hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_sub_of_values finalState leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState rightEntryState finalState "sub" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindSub (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_right_threaded_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.sub) (mkIR := fun a b => YulExpr.call "sub" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hright hcompile hsource hir

theorem exprInternalHelperCompositionalPostStateResult_sub_right_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState rightEntryState headState rightFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hright : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      right rightIR helperFuel irFuel runtime headRuntime rightEntryState headState
      rightFinalState rightValue)
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hsourceLeft : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime left = some leftValue)
    (hirLeft :
      evalIRExprWithInternals runtimeContract (irFuel + 1) parentState leftIR =
        .value leftValue rightEntryState)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) rightEntryState rightIR =
        .value rightValue finalState)
    (hfindSub : findInternalFunction? runtimeContract "sub" = none)
    (hfinalEq : finalState = rightFinalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.sub left right) (YulExpr.call "sub" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprSubValue leftValue rightValue) := by
  rcases hright with ⟨hrightResult, hrightRuntime, hrightExact, _hrightLt⟩
  subst hfinalEq
  refine ⟨?_, hrightRuntime, hrightExact, exprSubValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_sub_right_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (rightEntryState := rightEntryState)
      (headState := headState)
      hrightResult hcompileLeft hsourceLeft hirLeft hirRight hfindSub

theorem exprInternalHelperCompositionalContextResult_sub_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime right = some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindSub : findInternalFunction? runtimeContract "sub" = none) :
    ExprInternalHelperCompositionalContextResult runtimeContract spec fields
      (Expr.sub left right) (YulExpr.call "sub" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprSubValue leftValue rightValue) := by
  let value := exprSubValue leftValue rightValue
  have hleftFacts := hleft
  unfold ExprInternalHelperCompositionalContextResult at hleftFacts
  rcases hleftFacts with ⟨hcompileLeft, hsourceLeft, hirLeft, _, _⟩
  let hcompile := compileExprWithInternals_sub_of_children hcompileLeft hcompileRight
  let hsource := evalExprWithHelpers_sub_of_values spec fields (helperFuel + 1)
    runtime hsourceLeft hsourceRight
  let hbuiltin := evalBuiltinCallWithEvmYulLeanContext_sub_of_values finalState
    leftValue rightValue
  let hir := evalIRExprWithInternals_binary_builtin_of_values runtimeContract (irFuel + 1)
    parentState leftFinalState finalState "sub" leftIR rightIR leftValue rightValue value
    hirLeft hirRight hfindSub (by decide) (by decide) (by decide) hbuiltin
  exact
    exprInternalHelperCompositionalContextResult_binary_left_context
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (mkExpr := Expr.sub) (mkIR := fun a b => YulExpr.call "sub" [a, b])
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (state := parentState) (headState := headState)
      hleft hcompile hsource hir

theorem exprInternalHelperCompositionalPostStateResult_sub_left_threaded
    {runtimeContract : IRContract} {spec : CompilationModel} {fields : List Field}
    {scope : List String}
    {left right : Expr} {leftIR rightIR : YulExpr} {helperFuel irFuel : Nat}
    {runtime headRuntime : SourceSemantics.RuntimeState}
    {parentState headState leftFinalState finalState : IRState}
    {leftValue rightValue : Nat}
    (hleft : ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      left leftIR helperFuel irFuel runtime headRuntime parentState headState
      leftFinalState leftValue)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hsourceRight : SourceSemantics.evalExprWithHelpers spec fields (helperFuel + 1)
      runtime right = some rightValue)
    (hirRight :
      evalIRExprWithInternals runtimeContract (irFuel + 1) leftFinalState rightIR =
        .value rightValue finalState)
    (hfindSub : findInternalFunction? runtimeContract "sub" = none)
    (hfinalRuntime : FunctionBody.runtimeStateMatchesIR fields runtime finalState)
    (hfinalExact :
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState) :
    ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
      (Expr.sub left right) (YulExpr.call "sub" [leftIR, rightIR]) helperFuel irFuel
      runtime headRuntime parentState headState finalState
      (exprSubValue leftValue rightValue) := by
  rcases hleft with ⟨hleftResult, _, _, _⟩
  refine ⟨?_, hfinalRuntime, hfinalExact, exprSubValue_lt_evmModulus leftValue rightValue⟩
  exact
    exprInternalHelperCompositionalContextResult_sub_left_threaded
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
      (helperFuel := helperFuel) (irFuel := irFuel)
      (runtime := runtime) (headRuntime := headRuntime)
      (parentState := parentState) (headState := headState)
      hleftResult hcompileRight hsourceRight hirRight hfindSub

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
        sizeOf compiledIR - compiledIR.length ≤ irFuel →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope stmt)
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt)
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + irFuel + 1) state compiledIR)

/-- Spec-functions variant of `ExprInternalHelperHeadStepBridge`.

This closes the compile-shape gap for expression-position helper heads: the
statement compile obligation uses the same `spec.functions` internal-helper
environment carried by `compileExprWithInternals` payloads.  The legacy bridge
above is left unchanged for the existing generic interface, whose
`CompiledStmtStepWithHelpersAndHelperIR.compileOk` field still records the
default empty-internal-function compile shape. -/
structure ExprInternalHelperHeadStepBridgeWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (stmt : Stmt) : Prop where
  compile :
    ∀ {scope : List String},
      ∃ compiledIR,
        CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
            stmt spec.functions =
          Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {compiledIR : List YulStmt},
      CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
          stmt spec.functions =
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
        sizeOf compiledIR - compiledIR.length ≤ irFuel →
        stmtStepMatchesIRExecWithInternals fields
          (stmtNextScope scope stmt)
          (SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt)
          (execIRStmtsWithInternals runtimeContract
            (compiledIR.length + irFuel + 1) state compiledIR)

/-- `Stmt.letVar` compiler shape when the bound expression has already been
compiled through the helper-aware expression compiler. -/
theorem compileStmt_letVar_of_compileExprWithInternals
    {fields : List Field}
    {events : List EventDef}
    {errors : List ErrorDef}
    {scope : List String}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    {internalFunctions : List FunctionSpec}
    (hcompile :
      CompilationModel.compileExprWithInternals fields .calldata internalFunctions value =
        Except.ok valueIR) :
    CompilationModel.compileStmt fields events errors .calldata [] false scope []
        (Stmt.letVar name value) internalFunctions =
      Except.ok [YulStmt.let_ name valueIR] := by
  simp [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork, hcompile]

/-- The first concrete expression-to-statement-head adapter for #2080.

The expression compositional result supplies the source value, compiled
expression value, and the helper-call payload introduced in phases 6-9.  The
adapter adds only the `letVar` statement wrapper.  The statement-side compile
shape remains explicit because `CompiledStmtStepWithHelpersAndHelperIR` still
records the legacy `compileStmt ... stmt = ok ...` form with the default empty
internal-function list, while the expression payload records
`compileExprWithInternals ... spec.functions ...`.  Two post-expression facts
also remain explicit because `ExprInternalHelperCompositionalContextResult`
currently does not record them: the final IR state must still match the source
runtime, and the old scope bindings must still agree in that final IR state. -/
theorem exprInternalHelperHeadStepBridge_letVar_of_exprCompositionalResult
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hvalueCompileStmt :
      CompilationModel.compileExprWithInternals fields .calldata [] value =
        Except.ok valueIR)
    (hvalue :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∃ finalState valueNat,
          ExprInternalHelperCompositionalContextResult runtimeContract spec fields
            value valueIR (helperFuel - 1) (irFuel - 1) runtime runtime state state
            finalState valueNat ∧
          FunctionBody.runtimeStateMatchesIR fields runtime finalState ∧
          FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState ∧
          valueNat < Compiler.Constants.evmModulus)
    (hvalueNamesInScope :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∀ {n : String}, n ∈ collectExprNames value → n ∈ scope) :
    ExprInternalHelperHeadStepBridge runtimeContract spec fields (Stmt.letVar name value) := by
  refine ⟨?_, ?_⟩
  · intro scope
    exact ⟨[YulStmt.let_ name valueIR],
      compileStmt_letVar_of_compileExprWithInternals
        (events := spec.events) (errors := spec.errors) (scope := scope)
        (name := name) hvalueCompileStmt⟩
  · intro scope compiledIR hcompile runtime state helperFuel irFuel hfuelPos
      hexact hscope hbounded hruntime hslack
    have hcompiledEq : compiledIR = [YulStmt.let_ name valueIR] := by
      have hshape :=
        compileStmt_letVar_of_compileExprWithInternals
          (events := spec.events) (errors := spec.errors) (scope := scope)
          (name := name) hvalueCompileStmt
      exact Except.ok.inj (hcompile.symm.trans hshape)
    subst hcompiledEq
    have hirFuelPos : 0 < irFuel := by
      have hsize : sizeOf [YulStmt.let_ name valueIR] ≥ 2 := by
        simp
      simp at hslack
      omega
    rcases hvalue (scope := scope) (runtime := runtime) (state := state)
        (helperFuel := helperFuel) (irFuel := irFuel) hfuelPos hirFuelPos
        hexact hscope hbounded hruntime with
      ⟨finalState, valueNat, hresult, hfinalRuntime, hfinalExact, hvalueLt⟩
    have hresultFacts := hresult
    unfold ExprInternalHelperCompositionalContextResult at hresultFacts
    rcases hresultFacts with ⟨_hcompileExpr, hsourceValue, hirValue, _, _helperPayload⟩
    have hhelperFuelEq : helperFuel - 1 + 1 = helperFuel := by
      omega
    have hirFuelEq : irFuel - 1 + 1 = irFuel := by
      omega
    rw [hhelperFuelEq] at hsourceValue
    rw [hirFuelEq] at hirValue
    let runtime' : SourceSemantics.RuntimeState :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' : IRState := finalState.setVar name valueNat
    have hsourceExec :
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.letVar name value) =
          .continue runtime' := by
      simp [SourceSemantics.execStmtWithHelpers, hsourceValue, runtime']
    have hirExec :
        execIRStmtsWithInternals runtimeContract
            ([YulStmt.let_ name valueIR].length + irFuel + 1) state
            [YulStmt.let_ name valueIR] =
          .continue state' := by
      have houter :
          [YulStmt.let_ name valueIR].length + irFuel + 1 =
            Nat.succ (Nat.succ irFuel) := by
        simp
        omega
      rw [houter]
      simp only [execIRStmtsWithInternals]
      simp [execIRStmtWithInternals, hirValue, state']
    have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' := by
      exact FunctionBody.runtimeStateMatchesIR_setVar_bindValue hfinalRuntime name valueNat
    have hexactBase : FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (name :: scope) runtime'.bindings state' :=
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hfinalExact
    have hnextIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (Stmt.letVar name value)) (name :: scope) := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with rfl | hn | hn
      · simp
      · exact List.mem_cons_of_mem _
          (hvalueNamesInScope hfuelPos hirFuelPos hexact hscope hbounded hruntime hn)
      · exact List.mem_cons_of_mem _ hn
    have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (stmtNextScope scope (Stmt.letVar name value)) runtime'.bindings state' :=
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexactBase hnextIncl
    have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
      FunctionBody.bindingsBounded_bindValue hbounded name valueNat hvalueLt
    have hscopeBase : FunctionBody.scopeNamesPresent (name :: scope) runtime'.bindings :=
      FunctionBody.scopeNamesPresent_cons_bindValue hscope
    have hscope' : FunctionBody.scopeNamesPresent
        (stmtNextScope scope (Stmt.letVar name value)) runtime'.bindings :=
      FunctionBody.scopeNamesPresent_of_included hscopeBase hnextIncl
    rw [hsourceExec, hirExec]
    exact ⟨hruntime', hexact', hbounded', hscope'⟩

/-- Spec-functions `Stmt.letVar` head adapter from a post-state expression
payload.  Unlike `exprInternalHelperHeadStepBridge_letVar_of_exprCompositionalResult`,
this bridge uses the same `spec.functions` compile shape as the expression
payload and consumes the post-expression source/IR state facts directly from
`ExprInternalHelperCompositionalPostStateResult`. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String}
    {value : Expr}
    {valueIR : YulExpr}
    (hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions value =
        Except.ok valueIR)
    (hvalue :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∃ finalState valueNat,
          ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
            value valueIR (helperFuel - 1) (irFuel - 1) runtime runtime state state
            finalState valueNat)
    (hvalueNamesInScope :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∀ {n : String}, n ∈ collectExprNames value → n ∈ scope) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name value) := by
  refine ⟨?_, ?_⟩
  · intro scope
    exact ⟨[YulStmt.let_ name valueIR],
      compileStmt_letVar_of_compileExprWithInternals
        (events := spec.events) (errors := spec.errors) (scope := scope)
        (name := name) hvalueCompileSpec⟩
  · intro scope compiledIR hcompile runtime state helperFuel irFuel hfuelPos
      hexact hscope hbounded hruntime hslack
    have hcompiledEq : compiledIR = [YulStmt.let_ name valueIR] := by
      have hshape :=
        compileStmt_letVar_of_compileExprWithInternals
          (events := spec.events) (errors := spec.errors) (scope := scope)
          (name := name) hvalueCompileSpec
      exact Except.ok.inj (hcompile.symm.trans hshape)
    subst hcompiledEq
    have hirFuelPos : 0 < irFuel := by
      have hsize : sizeOf [YulStmt.let_ name valueIR] ≥ 2 := by
        simp
      simp at hslack
      omega
    rcases hvalue (scope := scope) (runtime := runtime) (state := state)
        (helperFuel := helperFuel) (irFuel := irFuel) hfuelPos hirFuelPos
        hexact hscope hbounded hruntime with
      ⟨finalState, valueNat, hpost⟩
    rcases hpost with ⟨hresult, hfinalRuntime, hfinalExact, hvalueLt⟩
    have hresultFacts := hresult
    unfold ExprInternalHelperCompositionalContextResult at hresultFacts
    rcases hresultFacts with ⟨_hcompileExpr, hsourceValue, hirValue, _, _helperPayload⟩
    have hhelperFuelEq : helperFuel - 1 + 1 = helperFuel := by
      omega
    have hirFuelEq : irFuel - 1 + 1 = irFuel := by
      omega
    rw [hhelperFuelEq] at hsourceValue
    rw [hirFuelEq] at hirValue
    let runtime' : SourceSemantics.RuntimeState :=
      { runtime with bindings := SourceSemantics.bindValue runtime.bindings name valueNat }
    let state' : IRState := finalState.setVar name valueNat
    have hsourceExec :
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.letVar name value) =
          .continue runtime' := by
      simp [SourceSemantics.execStmtWithHelpers, hsourceValue, runtime']
    have hirExec :
        execIRStmtsWithInternals runtimeContract
            ([YulStmt.let_ name valueIR].length + irFuel + 1) state
            [YulStmt.let_ name valueIR] =
          .continue state' := by
      have houter :
          [YulStmt.let_ name valueIR].length + irFuel + 1 =
            Nat.succ (Nat.succ irFuel) := by
        simp
        omega
      rw [houter]
      simp only [execIRStmtsWithInternals]
      simp [execIRStmtWithInternals, hirValue, state']
    have hruntime' : FunctionBody.runtimeStateMatchesIR fields runtime' state' := by
      exact FunctionBody.runtimeStateMatchesIR_setVar_bindValue hfinalRuntime name valueNat
    have hexactBase : FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (name :: scope) runtime'.bindings state' :=
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_setVar_bindValue hfinalExact
    have hnextIncl : FunctionBody.scopeNamesIncluded
        (stmtNextScope scope (Stmt.letVar name value)) (name :: scope) := by
      intro n hn
      simp [stmtNextScope, collectStmtNames] at hn
      rcases hn with rfl | hn | hn
      · simp
      · exact List.mem_cons_of_mem _
          (hvalueNamesInScope hfuelPos hirFuelPos hexact hscope hbounded hruntime hn)
      · exact List.mem_cons_of_mem _ hn
    have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
        (stmtNextScope scope (Stmt.letVar name value)) runtime'.bindings state' :=
      FunctionBody.bindingsExactlyMatchIRVarsOnScope_of_included hexactBase hnextIncl
    have hbounded' : FunctionBody.bindingsBounded runtime'.bindings :=
      FunctionBody.bindingsBounded_bindValue hbounded name valueNat hvalueLt
    have hscopeBase : FunctionBody.scopeNamesPresent (name :: scope) runtime'.bindings :=
      FunctionBody.scopeNamesPresent_cons_bindValue hscope
    have hscope' : FunctionBody.scopeNamesPresent
        (stmtNextScope scope (Stmt.letVar name value)) runtime'.bindings :=
      FunctionBody.scopeNamesPresent_of_included hscopeBase hnextIncl
    rw [hsourceExec, hirExec]
    exact ⟨hruntime', hexact', hbounded', hscope'⟩

/-- Concrete spec-functions `Stmt.letVar` bridge for a value expression of the
form `Expr.add left right` when the helper payload is in the right operand.
This instantiates the statement-head adapter with the phase-9 constructor
bridge and the post-state companion above. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_add_right_threaded
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String}
    {left right : Expr}
    {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hvalue :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∃ rightEntryState finalState leftValue rightValue,
          SourceSemantics.evalExprWithHelpers spec fields (helperFuel - 1 + 1)
              runtime left =
            some leftValue ∧
          evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) state leftIR =
            .value leftValue rightEntryState ∧
          ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
            right rightIR (helperFuel - 1) (irFuel - 1) runtime runtime
            rightEntryState state finalState rightValue ∧
          evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) rightEntryState rightIR =
            .value rightValue finalState ∧
          findInternalFunction? runtimeContract "add" = none)
    (hvalueNamesInScope :
      ∀ {scope : List String}
        {runtime : SourceSemantics.RuntimeState}
        {state : IRState}
        {helperFuel irFuel : Nat},
        0 < helperFuel →
        0 < irFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        ∀ {n : String}, n ∈ collectExprNames (Expr.add left right) → n ∈ scope) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name (Expr.add left right)) := by
  have hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.add left right) =
        Except.ok (YulExpr.call "add" [leftIR, rightIR]) :=
    compileExprWithInternals_add_of_children hcompileLeft hcompileRight
  exact
    exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (name := name) (value := Expr.add left right)
      (valueIR := YulExpr.call "add" [leftIR, rightIR])
      hvalueCompileSpec
      (fun {scope} {runtime} {state} {helperFuel} {irFuel}
          hfuelPos hirFuelPos hexact hscope hbounded hruntime => by
        rcases hvalue (scope := scope) (runtime := runtime) (state := state)
            (helperFuel := helperFuel) (irFuel := irFuel)
            hfuelPos hirFuelPos hexact hscope hbounded hruntime with
          ⟨rightEntryState, finalState, leftValue, rightValue,
            hsourceLeft, hirLeft, hrightPost, hirRight, hfindAdd⟩
        refine ⟨finalState, exprAddValue leftValue rightValue, ?_⟩
        exact
          exprInternalHelperCompositionalPostStateResult_add_right_threaded
            (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
            (scope := scope)
            (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
            (helperFuel := helperFuel - 1) (irFuel := irFuel - 1)
            (runtime := runtime) (headRuntime := runtime)
            (parentState := state) (rightEntryState := rightEntryState)
            (headState := state)
            hrightPost hcompileLeft hsourceLeft hirLeft hirRight hfindAdd rfl)
      hvalueNamesInScope

/-- Payload needed to lift a left-helper `Expr.add` into a `Stmt.letVar`
expression-head bridge. -/
def LetVarAddLeftThreadedEvidence
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (left right : Expr)
    (leftIR rightIR : YulExpr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∃ leftFinalState finalState leftValue rightValue,
      ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
        left leftIR (helperFuel - 1) (irFuel - 1) runtime runtime
        state state leftFinalState leftValue ∧
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel - 1 + 1)
          runtime right =
        some rightValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) leftFinalState rightIR =
        .value rightValue finalState ∧
      findInternalFunction? runtimeContract "add" = none ∧
      FunctionBody.runtimeStateMatchesIR fields runtime finalState ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState

/-- Scope-name evidence for `Stmt.letVar` expression-head add bridges. -/
def LetVarAddNamesInScopeEvidence
    (_spec : CompilationModel)
    (fields : List Field)
    (left right : Expr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∀ {n : String}, n ∈ collectExprNames (Expr.add left right) → n ∈ scope

/-- Concrete spec-functions `Stmt.letVar` bridge for a value expression of the
form `Expr.add left right` when the helper payload is in the left operand. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_add_left_threaded
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String} {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hvalue :
      LetVarAddLeftThreadedEvidence runtimeContract spec fields left right leftIR rightIR)
    (hvalueNamesInScope : LetVarAddNamesInScopeEvidence spec fields left right) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name (Expr.add left right)) := by
  have hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.add left right) =
        Except.ok (YulExpr.call "add" [leftIR, rightIR]) :=
    compileExprWithInternals_add_of_children hcompileLeft hcompileRight
  exact
    exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (name := name) (value := Expr.add left right)
      (valueIR := YulExpr.call "add" [leftIR, rightIR])
      hvalueCompileSpec
      (fun {scope} {runtime} {state} {helperFuel} {irFuel}
          hfuelPos hirFuelPos hexact hscope hbounded hruntime => by
        rcases hvalue (scope := scope) (runtime := runtime) (state := state)
            (helperFuel := helperFuel) (irFuel := irFuel)
            hfuelPos hirFuelPos hexact hscope hbounded hruntime with
          ⟨leftFinalState, finalState, leftValue, rightValue,
            hleftPost, hsourceRight, hirRight, hfindAdd, hfinalRuntime, hfinalExact⟩
        refine ⟨finalState, exprAddValue leftValue rightValue, ?_⟩
        exact
          exprInternalHelperCompositionalPostStateResult_add_left_threaded
            (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
            (scope := scope)
            (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
            (helperFuel := helperFuel - 1) (irFuel := irFuel - 1)
            (runtime := runtime) (headRuntime := runtime)
            (parentState := state) (headState := state)
            hleftPost hcompileRight hsourceRight hirRight hfindAdd
            hfinalRuntime hfinalExact)
      hvalueNamesInScope

/-- Payload needed to lift a right-helper `Expr.mul` into a `Stmt.letVar`
expression-head bridge. -/
def LetVarMulRightThreadedEvidence
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (left right : Expr)
    (leftIR rightIR : YulExpr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∃ rightEntryState finalState leftValue rightValue,
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel - 1 + 1)
          runtime left =
        some leftValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) state leftIR =
        .value leftValue rightEntryState ∧
      ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
        right rightIR (helperFuel - 1) (irFuel - 1) runtime runtime
        rightEntryState state finalState rightValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) rightEntryState rightIR =
        .value rightValue finalState ∧
      findInternalFunction? runtimeContract "mul" = none

/-- Scope-name evidence for `Stmt.letVar` expression-head mul bridges. -/
def LetVarMulNamesInScopeEvidence
    (_spec : CompilationModel)
    (fields : List Field)
    (left right : Expr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∀ {n : String}, n ∈ collectExprNames (Expr.mul left right) → n ∈ scope

/-- Concrete spec-functions `Stmt.letVar` bridge for a value expression of the
form `Expr.mul left right` when the helper payload is in the right operand. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_mul_right_threaded
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String} {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hvalue :
      LetVarMulRightThreadedEvidence runtimeContract spec fields left right leftIR rightIR)
    (hvalueNamesInScope : LetVarMulNamesInScopeEvidence spec fields left right) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name (Expr.mul left right)) := by
  have hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.mul left right) =
        Except.ok (YulExpr.call "mul" [leftIR, rightIR]) :=
    compileExprWithInternals_mul_of_children hcompileLeft hcompileRight
  exact
    exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (name := name) (value := Expr.mul left right)
      (valueIR := YulExpr.call "mul" [leftIR, rightIR])
      hvalueCompileSpec
      (fun {scope} {runtime} {state} {helperFuel} {irFuel}
          hfuelPos hirFuelPos hexact hscope hbounded hruntime => by
        rcases hvalue (scope := scope) (runtime := runtime) (state := state)
            (helperFuel := helperFuel) (irFuel := irFuel)
            hfuelPos hirFuelPos hexact hscope hbounded hruntime with
          ⟨rightEntryState, finalState, leftValue, rightValue,
            hsourceLeft, hirLeft, hrightPost, hirRight, hfindMul⟩
        refine ⟨finalState, exprMulValue leftValue rightValue, ?_⟩
        exact
          exprInternalHelperCompositionalPostStateResult_mul_right_threaded
            (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
            (scope := scope)
            (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
            (helperFuel := helperFuel - 1) (irFuel := irFuel - 1)
            (runtime := runtime) (headRuntime := runtime)
            (parentState := state) (rightEntryState := rightEntryState)
            (headState := state)
            hrightPost hcompileLeft hsourceLeft hirLeft hirRight hfindMul rfl)
      hvalueNamesInScope

/-- Payload needed to lift a left-helper `Expr.mul` into a `Stmt.letVar`
expression-head bridge. -/
def LetVarMulLeftThreadedEvidence
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (left right : Expr)
    (leftIR rightIR : YulExpr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∃ leftFinalState finalState leftValue rightValue,
      ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
        left leftIR (helperFuel - 1) (irFuel - 1) runtime runtime
        state state leftFinalState leftValue ∧
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel - 1 + 1)
          runtime right =
        some rightValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) leftFinalState rightIR =
        .value rightValue finalState ∧
      findInternalFunction? runtimeContract "mul" = none ∧
      FunctionBody.runtimeStateMatchesIR fields runtime finalState ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings finalState

/-- Concrete spec-functions `Stmt.letVar` bridge for a value expression of the
form `Expr.mul left right` when the helper payload is in the left operand. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_mul_left_threaded
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String} {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hvalue :
      LetVarMulLeftThreadedEvidence runtimeContract spec fields left right leftIR rightIR)
    (hvalueNamesInScope : LetVarMulNamesInScopeEvidence spec fields left right) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name (Expr.mul left right)) := by
  have hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.mul left right) =
        Except.ok (YulExpr.call "mul" [leftIR, rightIR]) :=
    compileExprWithInternals_mul_of_children hcompileLeft hcompileRight
  exact
    exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (name := name) (value := Expr.mul left right)
      (valueIR := YulExpr.call "mul" [leftIR, rightIR])
      hvalueCompileSpec
      (fun {scope} {runtime} {state} {helperFuel} {irFuel}
          hfuelPos hirFuelPos hexact hscope hbounded hruntime => by
        rcases hvalue (scope := scope) (runtime := runtime) (state := state)
            (helperFuel := helperFuel) (irFuel := irFuel)
            hfuelPos hirFuelPos hexact hscope hbounded hruntime with
          ⟨leftFinalState, finalState, leftValue, rightValue,
            hleftPost, hsourceRight, hirRight, hfindMul, hfinalRuntime, hfinalExact⟩
        refine ⟨finalState, exprMulValue leftValue rightValue, ?_⟩
        exact
          exprInternalHelperCompositionalPostStateResult_mul_left_threaded
            (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
            (scope := scope)
            (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
            (helperFuel := helperFuel - 1) (irFuel := irFuel - 1)
            (runtime := runtime) (headRuntime := runtime)
            (parentState := state) (headState := state)
            hleftPost hcompileRight hsourceRight hirRight hfindMul
            hfinalRuntime hfinalExact)
      hvalueNamesInScope

/-- Payload needed to lift a right-helper `Expr.sub` into a `Stmt.letVar`
expression-head bridge. -/
def LetVarSubRightThreadedEvidence
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (left right : Expr)
    (leftIR rightIR : YulExpr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∃ rightEntryState finalState leftValue rightValue,
      SourceSemantics.evalExprWithHelpers spec fields (helperFuel - 1 + 1)
          runtime left =
        some leftValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) state leftIR =
        .value leftValue rightEntryState ∧
      ExprInternalHelperCompositionalPostStateResult runtimeContract spec fields scope
        right rightIR (helperFuel - 1) (irFuel - 1) runtime runtime
        rightEntryState state finalState rightValue ∧
      evalIRExprWithInternals runtimeContract (irFuel - 1 + 1) rightEntryState rightIR =
        .value rightValue finalState ∧
      findInternalFunction? runtimeContract "sub" = none

/-- Scope-name evidence for `Stmt.letVar` expression-head sub bridges. -/
def LetVarSubNamesInScopeEvidence
    (_spec : CompilationModel)
    (fields : List Field)
    (left right : Expr) : Prop :=
  ∀ {scope : List String}
    {runtime : SourceSemantics.RuntimeState}
    {state : IRState}
    {helperFuel irFuel : Nat},
    0 < helperFuel →
    0 < irFuel →
    FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
    FunctionBody.scopeNamesPresent scope runtime.bindings →
    FunctionBody.bindingsBounded runtime.bindings →
    FunctionBody.runtimeStateMatchesIR fields runtime state →
    ∀ {n : String}, n ∈ collectExprNames (Expr.sub left right) → n ∈ scope

/-- Concrete spec-functions `Stmt.letVar` bridge for a value expression of the
form `Expr.sub left right` when the helper payload is in the right operand. -/
theorem exprInternalHelperHeadStepBridgeWithInternals_letVar_sub_right_threaded
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {name : String} {left right : Expr} {leftIR rightIR : YulExpr}
    (hcompileLeft :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions left =
        Except.ok leftIR)
    (hcompileRight :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions right =
        Except.ok rightIR)
    (hvalue :
      LetVarSubRightThreadedEvidence runtimeContract spec fields left right leftIR rightIR)
    (hvalueNamesInScope : LetVarSubNamesInScopeEvidence spec fields left right) :
    ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields
      (Stmt.letVar name (Expr.sub left right)) := by
  have hvalueCompileSpec :
      CompilationModel.compileExprWithInternals fields .calldata spec.functions
          (Expr.sub left right) =
        Except.ok (YulExpr.call "sub" [leftIR, rightIR]) :=
    compileExprWithInternals_sub_of_children hcompileLeft hcompileRight
  exact
    exprInternalHelperHeadStepBridgeWithInternals_letVar_of_exprPostStateResult
      (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
      (name := name) (value := Expr.sub left right)
      (valueIR := YulExpr.call "sub" [leftIR, rightIR])
      hvalueCompileSpec
      (fun {scope} {runtime} {state} {helperFuel} {irFuel}
          hfuelPos hirFuelPos hexact hscope hbounded hruntime => by
        rcases hvalue (scope := scope) (runtime := runtime) (state := state)
            (helperFuel := helperFuel) (irFuel := irFuel)
            hfuelPos hirFuelPos hexact hscope hbounded hruntime with
          ⟨rightEntryState, finalState, leftValue, rightValue,
            hsourceLeft, hirLeft, hrightPost, hirRight, hfindSub⟩
        refine ⟨finalState, exprSubValue leftValue rightValue, ?_⟩
        exact
          exprInternalHelperCompositionalPostStateResult_sub_right_threaded
            (runtimeContract := runtimeContract) (spec := spec) (fields := fields)
            (scope := scope)
            (left := left) (right := right) (leftIR := leftIR) (rightIR := rightIR)
            (helperFuel := helperFuel - 1) (irFuel := irFuel - 1)
            (runtime := runtime) (headRuntime := runtime)
            (parentState := state) (rightEntryState := rightEntryState)
            (headState := state)
            hrightPost hcompileLeft hsourceLeft hirLeft hirRight hfindSub rfl)
      hvalueNamesInScope

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
  refine ⟨compiledIR, ?_⟩
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  exact ⟨_, _, rfl, rfl,
    hbridge.bridge (scope := scope) (compiledIR := compiledIR) hcompile
      runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack⟩

/-- Spec-functions-aware singleton statement proof for an expression-position
helper head.

This is the mechanical composition point for the phase-11
`ExprInternalHelperHeadStepBridgeWithInternals`/`Stmt.letVar` adapter.  It
records the same `spec.functions` compile shape as the expression helper
payload, avoiding the unsound conversion to the legacy default-empty internal
function compiler argument.  The remaining generic-list blocker is an
internal-functions-parametric analogue of the scope/list compilation lemmas
used by `compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR`. -/
theorem compiledStmtStepWithHelpersAndHelperIRWithInternals_of_exprHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    (hbridge :
      ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields stmt) :
    ∃ compiledIR,
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract
        spec
        fields
        scope
        stmt
        compiledIR := by
  rcases hbridge.compile (scope := scope) with ⟨compiledIR, hcompile⟩
  refine ⟨compiledIR, ?_⟩
  refine { compileOk := hcompile, preserves := ?_ }
  intro runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack
  exact ⟨_, _, rfl, rfl,
    hbridge.bridge (scope := scope) (compiledIR := compiledIR) hcompile
      runtime state helperFuel extraFuel hfuelPos hexact hscope hbounded hruntime hslack⟩

/-- Compose a spec-functions statement-head bridge into the new exact-scope
spec-functions list seam.  This is the first statement-list-level composition
point for the phase-12 `CompiledStmtStepWithHelpersAndHelperIRWithInternals`
witness; the full arbitrary-scope generic list theorem still needs the
`internalFunctions`-parametric scope-lifting API named in
`compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIRWithInternals_exact`. -/
theorem stmtListGenericWithHelpersAndHelperIRWithInternals_cons_of_exprHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    (hbridge :
      ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields stmt)
    (hrest :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields (stmtNextScope scope stmt) rest) :
    StmtListGenericWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope (stmt :: rest) := by
  rcases
      compiledStmtStepWithHelpersAndHelperIRWithInternals_of_exprHeadStepBridgeWithInternals
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmt := stmt)
        hbridge with
    ⟨compiledIR, hstep⟩
  exact .cons hstep hrest

/-- Build the spec-functions expression-helper list interface from a
`WithInternals` expression-head bridge at the current head. -/
theorem stmtListExprInternalHelperStepInterfaceWithInternals_cons_of_exprHeadStepBridgeWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {rest : List Stmt}
    (hbridge :
      ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields stmt)
    (hrest :
      StmtListExprInternalHelperStepInterfaceWithInternals
        runtimeContract
        spec
        fields
        (stmtNextScope scope stmt)
        rest) :
    StmtListExprInternalHelperStepInterfaceWithInternals
      runtimeContract
      spec
      fields
      scope
      (stmt :: rest) := by
  rcases
      compiledStmtStepWithHelpersAndHelperIRWithInternals_of_exprHeadStepBridgeWithInternals
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

/-- Assemble the spec-functions expression-helper interface from exact
`WithInternals` bridges for each expression-helper head in the list. -/
theorem stmtListExprInternalHelperStepInterfaceWithInternals_of_exprHeadStepBridgesWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hbridge :
      ∀ {stmt : Stmt},
        stmt ∈ stmts →
        stmtTouchesExprInternalHelperSurface stmt = true →
        ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields stmt) :
    StmtListExprInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hexpr
        exact
          compiledStmtStepWithHelpersAndHelperIRWithInternals_of_exprHeadStepBridgeWithInternals
            (runtimeContract := runtimeContract)
            (spec := spec)
            (fields := fields)
            (scope := scope)
            (stmt := stmt)
            (hbridge (by simp) hexpr)
      · apply ih
        intro stmt' hmem hexpr
        exact hbridge (List.mem_cons_of_mem _ hmem) hexpr

/-- Whole-list exact-scope assembler for statement lists whose heads all have
spec-functions bridges.  This is intentionally a narrow scaffold: mixed
helper-free/direct/residual list assembly still targets the legacy
`StmtListGenericWithHelpersAndHelperIR` until the remaining scope-reconstruction
lemmas are internal-functions-parametric. -/
theorem stmtListGenericWithHelpersAndHelperIRWithInternals_of_exprHeadStepBridges
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface :
      ∀ stmt ∈ stmts, stmtTouchesExprInternalHelperSurface stmt = true)
    (hbridge :
      ∀ {stmt : Stmt},
        stmt ∈ stmts →
        ExprInternalHelperHeadStepBridgeWithInternals runtimeContract spec fields stmt) :
    StmtListGenericWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIRWithInternals_of_exprInternalHelperStepInterfaceWithInternals
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmts := stmts)
      (hexpr :=
        stmtListExprInternalHelperStepInterfaceWithInternals_of_exprHeadStepBridgesWithInternals
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (stmts := stmts)
          (fun {stmt} hmem _ => hbridge hmem))
      (hallExpr := hsurface)

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

/-- Build the spec-functions structural-helper interface from an exact
`WithInternals` compiled head and the structural tail witness. This packages the
structural recursion case without converting back to the legacy empty-helper
compiler world. -/
theorem stmtListStructuralInternalHelperStepInterfaceWithInternals_cons_of_compiledStep
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmt compiledIR)
    (hrest :
      StmtListStructuralInternalHelperStepInterfaceWithInternals
        runtimeContract spec fields (stmtNextScope scope stmt) rest) :
    StmtListStructuralInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope (stmt :: rest) := by
  refine .cons ?_ hrest
  intro _
  exact ⟨compiledIR, hstep⟩

/-- Concrete `WithInternals` structural witness for an `ite` head. The caller
supplies the exact spec-functions compiled-step proof for the recursive
statement form, and this packages it into the structural helper interface
without falling back to the legacy empty-helper compiler world. -/
theorem stmtListStructuralInternalHelperStepInterfaceWithInternals_cons_ite_of_compiledStep
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {cond : Expr}
    {thenBranch elseBranch : List Stmt}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope
          (Stmt.ite cond thenBranch elseBranch) compiledIR)
    (hrest :
      StmtListStructuralInternalHelperStepInterfaceWithInternals
        runtimeContract spec fields
          (stmtNextScope scope (Stmt.ite cond thenBranch elseBranch)) rest) :
    StmtListStructuralInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope
      (Stmt.ite cond thenBranch elseBranch :: rest) := by
  exact
    stmtListStructuralInternalHelperStepInterfaceWithInternals_cons_of_compiledStep
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmt := Stmt.ite cond thenBranch elseBranch)
      (compiledIR := compiledIR)
      (rest := rest)
      hstep
      hrest

/-- Concrete `WithInternals` structural witness for a `forEach` head. The exact
head step compiles against `spec.functions`, so the recursive structural case
can participate in the phase-17 mixed-list assembly route directly. -/
theorem stmtListStructuralInternalHelperStepInterfaceWithInternals_cons_forEach_of_compiledStep
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {varName : String}
    {count : Expr}
    {body : List Stmt}
    {compiledIR : List YulStmt}
    {rest : List Stmt}
    (hstep :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope
          (Stmt.forEach varName count body) compiledIR)
    (hrest :
      StmtListStructuralInternalHelperStepInterfaceWithInternals
        runtimeContract spec fields
          (stmtNextScope scope (Stmt.forEach varName count body)) rest) :
    StmtListStructuralInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope
      (Stmt.forEach varName count body :: rest) := by
  exact
    stmtListStructuralInternalHelperStepInterfaceWithInternals_cons_of_compiledStep
      (runtimeContract := runtimeContract)
      (spec := spec)
      (fields := fields)
      (scope := scope)
      (stmt := Stmt.forEach varName count body)
      (compiledIR := compiledIR)
      (rest := rest)
      hstep
      hrest

/-- Assemble the spec-functions structural-helper interface from exact
`WithInternals` head steps for the structural-helper heads that occur in the
statement list. -/
theorem stmtListStructuralInternalHelperStepInterfaceWithInternals_of_structuralHeadStepsWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hstep :
      ∀ {scope : List String} {stmt : Stmt},
        stmt ∈ stmts →
        stmtTouchesStructuralInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIRWithInternals
            runtimeContract spec fields scope stmt compiledIR) :
    StmtListStructuralInternalHelperStepInterfaceWithInternals
      runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      refine .cons ?_ ?_
      · intro hstruct
        exact hstep (scope := scope) (stmt := stmt) (by simp) hstruct
      · apply ih
        intro scope' stmt' hmem hstruct
        exact hstep (scope := scope') (stmt := stmt')
          (List.mem_cons_of_mem stmt hmem) hstruct

/-- Full spec-functions-aware assembly from the split helper interfaces into
the exact `WithInternals` statement-list witness. This is the mixed-list
counterpart of `fullHelperAwareListWitness_of_allInterfaces`; it avoids the
legacy/default-empty helper-world list seam when callers provide exact
`WithInternals` head witnesses for helper-free and helper-surface heads. -/
theorem fullHelperAwareListWitnessWithInternals_of_allInterfaces
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree :
      StmtListHelperFreeStepInterfaceWithInternals
        runtimeContract spec fields scope stmts)
    (hcall :
      StmtListDirectInternalHelperCallStepInterfaceWithInternals
        runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterfaceWithInternals
        runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterfaceWithInternals
        runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterfaceWithInternals
        runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterfaceWithInternals
        runtimeContract spec fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIRWithInternals
      runtimeContract spec fields scope stmts :=
  stmtListGenericWithHelpersAndHelperIRWithInternals_of_helperFreeStepInterfaceWithInternals_and_directInternalHelperStepInterfaceWithInternals_and_exprInternalHelperStepInterfaceWithInternals_and_structuralInternalHelperStepInterfaceWithInternals_and_residualHelperSurfaceStepInterfaceWithInternals
    hhelperFree
    (stmtListDirectInternalHelperStepInterfaceWithInternals_of_callStepInterfaceWithInternals_and_assignStepInterfaceWithInternals
      hcall hassign)
    hexpr
    hstruct
    hresidual

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
