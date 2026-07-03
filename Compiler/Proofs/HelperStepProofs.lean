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
