import Compiler.Proofs.IRGeneration.GenericInduction.LegacyCompatibility

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

theorem stmtListHelperFreeStepInterface_of_core
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts) :
    StmtListHelperFreeStepInterface fields scope stmts := by
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep htail ih =>
      refine .cons ?_ ih
      intro _
      exact ⟨compiledIR, hstep⟩

/-- Event head-step inventory for the exact generic induction seam. The
event-aware contract-surface predicate supplies the support and expression
closure facts; the catalog supplies the actual compiled-step proof for a direct
`.emit` head. -/
structure EventHeadStepCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : Prop where
  emit :
    ∀ {scope : List String} {eventName : String} {args : List Expr},
      eventEmissionProofSupported spec.events eventName args = true →
      args.any exprTouchesUnsupportedContractSurface = false →
      ∃ compiledIR,
        CompiledStmtStepWithHelpersAndHelperIR
          runtimeContract spec fields scope (Stmt.emit eventName args) compiledIR

/-- Split event-head inventory for the final `.emit` proof.

`compile` is the pure `compileEmit` shape/success side; `bridge` is the
source/IR execution alignment for the compiled head. Keeping them separate
lets the next proof step focus on `compileEmit` without also rebuilding the
`CompiledStmtStepWithHelpersAndHelperIR` wrapper. -/
structure EventHeadStepBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : Prop where
  compile :
    ∀ {scope : List String} {eventName : String} {args : List Expr},
      eventEmissionProofSupported spec.events eventName args = true →
      args.any exprTouchesUnsupportedContractSurface = false →
      ∃ compiledIR,
        CompilationModel.compileStmt fields spec.events spec.errors .calldata
          [] false scope [] (Stmt.emit eventName args) = Except.ok compiledIR
  bridge :
    ∀ {scope : List String} {eventName : String} {args : List Expr}
        {compiledIR : List YulStmt},
      eventEmissionProofSupported spec.events eventName args = true →
      args.any exprTouchesUnsupportedContractSurface = false →
      CompilationModel.compileStmt fields spec.events spec.errors .calldata
        [] false scope [] (Stmt.emit eventName args) = Except.ok compiledIR →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (extraFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf compiledIR - compiledIR.length ≤ extraFuel →
        ∃ sourceResult irExec,
          SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.emit eventName args) = sourceResult ∧
          execIRStmtsWithInternals runtimeContract
            (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
          stmtStepMatchesIRExecWithInternals
            fields (stmtNextScope scope (Stmt.emit eventName args))
            sourceResult irExec

/-- Event-head inventory after the scalar `.emit` compile-shape theorem has
discharged the pure compile side. Future proof work only has to provide the
semantic bridge between source event execution and the compiled IR log. -/
structure EventHeadStepSemanticBridgeCatalog
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : Prop where
  bridge :
    ∀ {scope : List String} {eventName : String} {args : List Expr}
        {compiledIR : List YulStmt},
      eventEmissionProofSupported spec.events eventName args = true →
      args.any exprTouchesUnsupportedContractSurface = false →
      CompilationModel.compileStmt fields spec.events spec.errors .calldata
        [] false scope [] (Stmt.emit eventName args) = Except.ok compiledIR →
      ∀ (runtime : SourceSemantics.RuntimeState)
        (state : IRState)
        (helperFuel : Nat)
        (extraFuel : Nat),
        0 < helperFuel →
        FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
        FunctionBody.scopeNamesPresent scope runtime.bindings →
        FunctionBody.bindingsBounded runtime.bindings →
        FunctionBody.runtimeStateMatchesIR fields runtime state →
        sizeOf compiledIR - compiledIR.length ≤ extraFuel →
        ∃ sourceResult irExec,
          SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime
            (Stmt.emit eventName args) = sourceResult ∧
          execIRStmtsWithInternals runtimeContract
            (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
          stmtStepMatchesIRExecWithInternals
            fields (stmtNextScope scope (Stmt.emit eventName args))
            sourceResult irExec

/-- Mechanical wrapper from split event-head compile/execution obligations into
the existing event-head step catalog consumed by the list interface. -/
theorem eventHeadStepCatalog_of_bridgeCatalog
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    (hbridge : EventHeadStepBridgeCatalog runtimeContract spec fields) :
    EventHeadStepCatalog runtimeContract spec fields := by
  refine ⟨?_⟩
  intro scope eventName args hsupport hsurface
  rcases hbridge.compile
      (scope := scope)
      (eventName := eventName)
      (args := args)
      hsupport hsurface with
    ⟨compiledIR, hcompile⟩
  refine ⟨compiledIR, ?_⟩
  exact {
    compileOk := hcompile
    preserves := hbridge.bridge
      (scope := scope)
      (eventName := eventName)
      (args := args)
      (compiledIR := compiledIR)
      hsupport hsurface hcompile }

/-- Assemble the direct-event list interface from a reusable event head-step
catalog and the event-aware contract-surface gate. This is the structural bridge
that lets the generic proof consume a real `compiledStmtStep_emit` proof later
instead of eliminating `SupportedStmtList.emitEvent` by contradiction. -/
theorem stmtListEventSurfaceStepInterface_of_eventHeadStepCatalog_of_surfaceWithEvents
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hcatalog : EventHeadStepCatalog runtimeContract spec fields)
    (hsurface : stmtListTouchesUnsupportedContractSurfaceWithEvents spec.events stmts = false) :
    StmtListEventSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedContractSurfaceWithEvents] using hsurface
      have hstmtSurface :
          stmtTouchesUnsupportedContractSurfaceWithEvents spec.events stmt = false := hsplit.1
      have hrestSurface :
          stmtListTouchesUnsupportedContractSurfaceWithEvents spec.events rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hevent
      cases stmt with
      | emit eventName args =>
          exact hcatalog.emit
            (eventName := eventName)
            (args := args)
            (eventEmissionProofSupported_eq_true_of_emit_contractSurfaceWithEventsClosed
              hstmtSurface)
            (exprListTouchesUnsupportedContractSurface_eq_false_of_emit_contractSurfaceWithEventsClosed
              hstmtSurface)
      | _ =>
          simp [stmtTouchesEventSurface] at hevent

/-- Helper-surface-closed statement lists satisfy the exact helper-surface step
interface vacuously: no head ever needs a genuinely new helper-aware step
proof. -/
theorem stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

/-- Helper-surface-closed statement lists also satisfy the narrower exact
internal-helper step interface vacuously. -/
theorem stmtListInternalHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtInternal : stmtTouchesInternalHelperSurface stmt = false :=
        stmtTouchesInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtInternal] at hhelper
      cases hhelper

/-- Helper-surface-closed statement lists also satisfy the direct
statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtDirect : stmtTouchesDirectInternalHelperCallSurface stmt = false :=
        stmtTouchesDirectInternalHelperCallSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

/-- Direct-call-surface-closed statement lists satisfy the direct helper-call
exact-step interface vacuously. This is the narrower closure fact needed when a
body is allowed to use only helper-return bindings. -/
theorem stmtListDirectInternalHelperCallStepInterface_of_directCallSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesDirectInternalHelperCallSurface stmts = false) :
    StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesDirectInternalHelperCallSurface] using hsurface
      have hstmtSurface : stmtTouchesDirectInternalHelperCallSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesDirectInternalHelperCallSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

/-- Helper-surface-closed statement lists also satisfy the direct helper-return
binding interface vacuously. -/
theorem stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtDirect : stmtTouchesDirectInternalHelperAssignSurface stmt = false :=
        stmtTouchesDirectInternalHelperAssignSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtDirect] at hhelper
      cases hhelper

/-- Assemble the coarser direct helper interface from the two source-summary
shapes it still contains: void helper statements and helper-return bindings. -/
theorem stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hcall :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope stmts)
    (hassign :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope stmts) :
    StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction hcall with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadCall htailCall ih =>
      cases hassign with
      | cons hheadAssign htailAssign =>
          refine .cons ?_ (ih htailAssign)
          intro hdirect
          by_cases hcallFalse : stmtTouchesDirectInternalHelperCallSurface stmt = false
          · have hassignTrue : stmtTouchesDirectInternalHelperAssignSurface stmt = true := by
              simpa [stmtTouchesDirectInternalHelperSurface_eq_split, hcallFalse] using hdirect
            exact hheadAssign hassignTrue
          · have hcallTrue : stmtTouchesDirectInternalHelperCallSurface stmt = true := by
              cases hcallStmt : stmtTouchesDirectInternalHelperCallSurface stmt <;>
                simp [hcallStmt] at hcallFalse ⊢
            exact hheadCall hcallTrue

/-- Helper-surface-closed statement lists also satisfy the direct
statement-position internal-helper interface vacuously. -/
theorem stmtListDirectInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  exact
    stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
      (stmtListDirectInternalHelperCallStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := stmts)
        hsurface)
      (stmtListDirectInternalHelperAssignStepInterface_of_helperSurfaceClosed
        (runtimeContract := runtimeContract)
        (spec := spec)
        (fields := fields)
        (scope := scope)
        (stmts := stmts)
        hsurface)

/-- Helper-surface-closed statement lists also satisfy the expression-position
internal-helper interface vacuously. -/
theorem stmtListExprInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtExpr : stmtTouchesExprInternalHelperSurface stmt = false :=
        stmtTouchesExprInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtExpr] at hhelper
      cases hhelper

/-- Expr-helper-surface-closed statement lists satisfy the expression-position
helper exact-step interface vacuously. -/
theorem stmtListExprInternalHelperStepInterface_of_exprSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesExprInternalHelperSurface stmts = false) :
    StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesExprInternalHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesExprInternalHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesExprInternalHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

/-- Helper-surface-closed statement lists also satisfy the structural
internal-helper interface vacuously. -/
theorem stmtListStructuralInternalHelperStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hstmtStructural : stmtTouchesStructuralInternalHelperSurface stmt = false :=
        stmtTouchesStructuralInternalHelperSurface_eq_false_of_helperSurfaceClosed hstmtSurface
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtStructural] at hhelper
      cases hhelper

/-- Structural-helper-surface-closed statement lists satisfy the structural
helper exact-step interface vacuously. -/
theorem stmtListStructuralInternalHelperStepInterface_of_structuralSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesStructuralInternalHelperSurface stmts = false) :
    StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesStructuralInternalHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesStructuralInternalHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesStructuralInternalHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper
      rw [hstmtSurface] at hhelper
      cases hhelper

/-- Assemble the coarse internal-helper interface from the narrower proof-cut
interfaces that match the actual proof obligations: direct helper statements,
expression-position helper calls, and recursive structural transport. -/
theorem stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hexpr :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope stmts)
    (hstruct :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope stmts) :
    StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction hdirect with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadDirect htailDirect ih =>
      cases hexpr with
      | cons hheadExpr htailExpr =>
          cases hstruct with
          | cons hheadStruct htailStruct =>
              refine .cons ?_ (ih htailExpr htailStruct)
              intro hhelper
              by_cases hdirectFalse : stmtTouchesDirectInternalHelperSurface stmt = false
              · by_cases hexprFalse : stmtTouchesExprInternalHelperSurface stmt = false
                · have hstructTrue : stmtTouchesStructuralInternalHelperSurface stmt = true := by
                    simpa [stmtTouchesInternalHelperSurface_eq_split, hdirectFalse, hexprFalse]
                      using hhelper
                  exact hheadStruct hstructTrue
                · have hexprTrue : stmtTouchesExprInternalHelperSurface stmt = true := by
                    cases hexprStmt : stmtTouchesExprInternalHelperSurface stmt <;>
                      simp [hexprStmt] at hexprFalse ⊢
                  exact hheadExpr hexprTrue
              · have hdirectTrue : stmtTouchesDirectInternalHelperSurface stmt = true := by
                  cases hdirectStmt : stmtTouchesDirectInternalHelperSurface stmt <;>
                    simp [hdirectStmt] at hdirectFalse ⊢
                exact hheadDirect hdirectTrue

/-- Helper-surface-closed statement lists also satisfy the residual non-helper
exact step interface vacuously. -/
theorem stmtListResidualHelperSurfaceStepInterface_of_helperSurfaceClosed
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction stmts generalizing scope with
  | nil =>
      exact .nil
  | cons stmt rest ih =>
      have hsplit := Bool.or_eq_false_iff.mp <| by
        simpa [stmtListTouchesUnsupportedHelperSurface] using hsurface
      have hstmtSurface : stmtTouchesUnsupportedHelperSurface stmt = false := hsplit.1
      have hrestSurface : stmtListTouchesUnsupportedHelperSurface rest = false := hsplit.2
      refine .cons ?_ (ih hrestSurface)
      intro hhelper _
      rw [hstmtSurface] at hhelper
      cases hhelper

/-- Assemble the coarse exact helper-surface step interface from the split
interfaces: genuine internal-helper heads are proved through the narrow helper
surface interface, while the residual coarse-surface heads are discharged
separately. -/
theorem stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts) :
    StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts := by
  induction hinternal with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadInternal htailInternal ih =>
      cases hresidual with
      | cons hheadResidual htailResidual =>
          refine .cons ?_ (ih htailResidual)
          intro hhelper
          by_cases hactual : stmtTouchesInternalHelperSurface stmt = true
          · exact hheadInternal hactual
          · have hactualFalse : stmtTouchesInternalHelperSurface stmt = false := by
              cases hactual' : stmtTouchesInternalHelperSurface stmt <;>
                simp [hactual'] at hactual ⊢
            exact hheadResidual hhelper hactualFalse

/-- Lift an existing helper-free generic statement-list proof into the
helper-aware induction world when the whole list is helper-surface closed. This
is the current fail-closed bridge from the legacy generic library to the new
helper-aware induction seam. -/
theorem stmtListGenericWithHelpers_of_core_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface.1)
        (ih hsurface.2)
theorem stmtListGenericWithHelpers_of_helperFreeStepInterface_and_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    StmtListGenericWithHelpers spec fields scope stmts := by
  induction hhelperFree with
  | nil =>
      exact .nil
  | @cons scope stmt rest hhead htail ih =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rcases hhead hsurface.1 with ⟨compiledIR, hstep⟩
      exact .cons
        (hstep.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface.1)
        (ih hsurface.2)

private theorem compiledStmtStepWithHelpers_preserves_withCompat
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hcompat : compiledIRWithInternalsCompat runtimeContract compiledIR) :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (helperFuel : Nat)
      (extraFuel : Nat),
      0 < helperFuel →
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = sourceResult ∧
        execIRStmtsWithInternals runtimeContract
          (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExecWithInternals
          fields (stmtNextScope scope stmt) sourceResult irExec := by
  intro runtime state helperFuel extraFuel _ hexact hscope hbounded hruntime hslack
  rcases hstep.preserves runtime state helperFuel extraFuel
      hexact hscope hbounded hruntime hslack with
    ⟨sourceResult, irExec, hsource, hir, hmatch⟩
  refine ⟨sourceResult, externalIRExecResultToWithInternals irExec, hsource, ?_, ?_⟩
  · simpa [externalIRExecResultToWithInternals, hir] using hcompat state extraFuel
  · exact stmtStepMatchesIRExecWithInternals_of_stmtStepMatchesIRExec hmatch

/-- Any helper-aware generic statement-step proof already closes the exact
helper-aware compiled-side step goal when the compiled head stays inside the
legacy-compatible external Yul subset and the runtime contract has no internal
helper table. This is the compiled-side fail-closed bridge from the current
theorem domain to the exact helper-aware induction seam. -/
theorem CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hlegacy : LegacyCompatibleExternalStmtList compiledIR)
    (hinternal : runtimeContract.internalFunctions = []) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    apply compiledStmtStepWithHelpers_preserves_withCompat hstep
    intro state extraFuel
    exact
      execIRStmtsWithInternals_eq_execIRStmts_of_stmtCompatibility runtimeContract
        (execIRStmtWithInternals_eq_execIRStmt_of_stmtSubgoals
          runtimeContract
          (interpretIRWithInternalsZeroConservativeExtensionStmtSubgoals_closed
            runtimeContract))
        hinternal
        (compiledIR.length + extraFuel + 1)
        state
        compiledIR
        hlegacy

/-- Disjoint-based bridge: any helper-aware generic statement-step proof closes
the exact helper-aware compiled-side step goal when the compiled IR is disjoint
from the internal function table.  Unlike `withHelperIR_of_legacyCompatible` this
does **not** require `runtimeContract.internalFunctions = []`. -/
theorem CompiledStmtStepWithHelpers.withHelperIR_of_callsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStepWithHelpers spec fields scope stmt compiledIR)
    (hdisjoint : YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR) :
    CompiledStmtStepWithHelpersAndHelperIR
      runtimeContract spec fields scope stmt compiledIR where
  compileOk := hstep.compileOk
  preserves := by
    apply compiledStmtStepWithHelpers_preserves_withCompat hstep
    intro state extraFuel
    exact
      execIRStmtsWithInternals_eq_execIRStmts_of_callsDisjoint runtimeContract
        (compiledIR.length + extraFuel + 1)
        state
        compiledIR
        hdisjoint

/-- Lift helper-aware statement-list proofs into the exact helper-aware compiled
induction seam on the current legacy-compatible compiled subset. This isolates
future helper-summary work to the genuinely new helper-call cases: already
proved helper-free cases can be reused directly once callers supply the
compiled-side legacy-compatibility witness. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_withHelpers_and_compiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericWithHelpers spec fields scope stmts)
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hgeneric with
  | nil =>
      exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hlegacy with
      | cons hhead htail =>
          exact .cons
            (hstep.withHelperIR_of_legacyCompatible
              (hhead compiledIR (by simpa [hnoEvents, hnoErrors] using hstep.compileOk))
              hinternal)
            (ih htail)

/-- Exact helper-aware list bridge that splits the remaining work cleanly:
helper-free heads still reuse the legacy generic step library plus the weaker
helper-free compiled compatibility witness, while helper-positive heads are
discharged only through a dedicated exact helper-aware step interface. -/
theorem
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hsteps with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hlegacy with
          | cons hheadLegacy htailLegacy =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · obtain ⟨compiledIR, hcore⟩ := hheadFree hsurface
                exact .cons
                  (CompiledStmtStepWithHelpers.withHelperIR_of_legacyCompatible
                    (hcore.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface)
                    (hheadLegacy hsurface compiledIR hcore.compileOk)
                    hinternal)
                  (ih htailFree htailLegacy)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                exact .cons hcompiled (ih htailFree htailLegacy)

/-- Disjoint-based exact helper-aware list bridge: helper-free heads reuse the
legacy generic step library plus the new disjointness witness, while
helper-positive heads are discharged through the dedicated step interface.
Unlike the `_helperFreeCompiledLegacyCompatible` variant, this does **not**
require `runtimeContract.internalFunctions = []`. -/
theorem
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hsteps with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadStep htailSteps ih =>
      cases hhelperFree with
      | cons hheadFree htailFree =>
          cases hdisjoint with
          | cons hheadDisjoint htailDisjoint =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · obtain ⟨compiledIR, hcore⟩ := hheadFree hsurface
                exact .cons
                  (CompiledStmtStepWithHelpers.withHelperIR_of_callsDisjoint
                    (hcore.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface)
                    (hheadDisjoint hsurface compiledIR hcore.compileOk))
                  (ih htailFree htailDisjoint)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;> simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                exact .cons hcompiled (ih htailFree htailDisjoint)

/-- Exact helper-aware list bridge with the helper-positive work split cleanly:
genuine internal-helper heads are supplied through a narrow helper-specific
interface, while residual coarse helper-surface heads are tracked separately so
future helper-summary proofs do not also inherit unrelated non-helper cases. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hhelperFree with
  | nil =>
      exact .nil
  | @cons scope stmt rest hheadFree htailFree ih =>
      cases hinternal with
      | cons hheadInternal htailInternal =>
          cases hresidual with
          | cons hheadResidual htailResidual =>
              cases hlegacy with
              | cons hheadLegacy htailLegacy =>
                  by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
                  · rcases hheadFree hsurface with ⟨compiledIR, hcore⟩
                    exact .cons
                      ((hcore.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface).withHelperIR_of_legacyCompatible
                        (hheadLegacy hsurface compiledIR hcore.compileOk)
                        hnoInternalFunctions)
                      (ih htailInternal htailResidual htailLegacy)
                  · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                      cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                        simp [hstmt] at hsurface ⊢
                    -- Combine the internal and residual interfaces for this head
                    have hheadStep : stmtTouchesUnsupportedHelperSurface stmt = true →
                        ∃ compiledIR,
                          CompiledStmtStepWithHelpersAndHelperIR
                            runtimeContract spec fields scope stmt compiledIR := by
                      intro _
                      by_cases hactual : stmtTouchesInternalHelperSurface stmt = true
                      · exact hheadInternal hactual
                      · have hactualFalse : stmtTouchesInternalHelperSurface stmt = false := by
                          cases hactual' : stmtTouchesInternalHelperSurface stmt <;>
                            simp [hactual'] at hactual ⊢
                        exact hheadResidual hsurfaceTrue hactualFalse
                    rcases hheadStep hsurfaceTrue with ⟨compiledIR, hcompiled⟩
                    exact .cons hcompiled (ih htailInternal htailResidual htailLegacy)

/-- Exact helper-aware list bridge over the fully split helper-positive
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are tracked separately, so future summary/rank proofs
can target the exact source-side obligation they discharge. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hinternal :=
        stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
            hcall hassign)
          hexpr
          hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions

/-- Exact helper-aware list bridge over the fully split helper-positive
interfaces: direct helper statements, expression-position helper heads, and
recursive structural heads are tracked separately, so future summary/rank proofs
can target the exact source-side obligation they discharge. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hhelperFree : StmtListHelperFreeStepInterface fields scope stmts)
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := hhelperFree)
      (hinternal :=
        stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
          hdirect
          hexpr
          hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions

/-- Exact helper-aware list bridge that splits the remaining work cleanly:
helper-free heads still reuse the legacy generic step library plus the weaker
helper-free compiled compatibility witness, while helper-positive heads are
discharged only through a dedicated exact helper-aware step interface. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hgeneric with
  | nil => exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hsteps with
      | cons hheadStep htailSteps =>
          cases hlegacy with
          | cons hheadLegacy htailLegacy =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · exact .cons
                  ((hstep.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface).withHelperIR_of_legacyCompatible
                    (hheadLegacy hsurface compiledIR hstep.compileOk) hinternal)
                  (ih htailSteps htailLegacy)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                    simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR', hcompiled⟩
                exact .cons hcompiled (ih htailSteps htailLegacy)

theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsteps : StmtListHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  induction hgeneric with
  | nil => exact .nil
  | @cons scope stmt compiledIR rest hstep hrest ih =>
      cases hsteps with
      | cons hheadStep htailSteps =>
          cases hdisjoint with
          | cons hheadDisjoint htailDisjoint =>
              by_cases hsurface : stmtTouchesUnsupportedHelperSurface stmt = false
              · exact .cons
                  ((hstep.withHelpers_of_helperSurfaceClosed hnoEvents hnoErrors hsurface).withHelperIR_of_callsDisjoint
                    (hheadDisjoint hsurface compiledIR hstep.compileOk))
                  (ih htailSteps htailDisjoint)
              · have hsurfaceTrue : stmtTouchesUnsupportedHelperSurface stmt = true := by
                  cases hstmt : stmtTouchesUnsupportedHelperSurface stmt <;>
                    simp [hstmt] at hsurface ⊢
                rcases hheadStep hsurfaceTrue with ⟨compiledIR', hcompiled⟩
                exact .cons hcompiled (ih htailSteps htailDisjoint)

/-- Exact helper-aware list bridge over the split helper-positive interfaces:
the legacy `StmtListGenericCore` witness is still reused for helper-free heads,
while genuine internal-helper heads and residual coarse helper-surface heads are
supplied separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hinternal :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hresidual :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope stmts)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hnoInternalFunctions : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hinternal := hinternal)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions

/-- Legacy-core exact helper-aware list bridge over the fully split
helper-positive interfaces. This keeps `StmtListGenericCore` reusable for
helper-free heads while future helper-rich work targets direct helper
statements, expression-position helper heads, and recursive structural heads
separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hcall := hcall)
      (hassign := hassign)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions

/-- Legacy-core exact helper-aware list bridge over the fully split
helper-positive interfaces. This keeps `StmtListGenericCore` reusable for
helper-free heads while future helper-rich work targets direct helper
statements, expression-position helper heads, and recursive structural heads
separately. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hdirect :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope stmts)
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_helperFreeStepInterface_and_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hhelperFree := stmtListHelperFreeStepInterface_of_core hgeneric)
      (hdirect := hdirect)
      (hexpr := hexpr)
      (hstruct := hstruct)
      (hresidual := hresidual)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hnoInternalFunctions

/-- Disjoint-based legacy-core exact helper-aware list bridge over the fully
split helper-positive interfaces.  Does **not** require
`runtimeContract.internalFunctions = []`. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_directInternalHelperCallStepInterface_and_directInternalHelperAssignStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface_and_residualHelperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
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
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_internalHelperSurfaceStepInterface_and_residualHelperSurfaceStepInterface
          (stmtListInternalHelperSurfaceStepInterface_of_directInternalHelperStepInterface_and_exprInternalHelperStepInterface_and_structuralInternalHelperStepInterface
            (stmtListDirectInternalHelperStepInterface_of_callStepInterface_and_assignStepInterface
              hcall
              hassign)
            hexpr
            hstruct)
          hresidual)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      (hdisjoint := hdisjoint)

/-- On helper-surface-closed statement lists, the disjoint-based bridge
collapses: no internal function table constraint at all is needed since every
head is helper-free and compiled-disjoint. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledCallsDisjoint
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hdisjoint : StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope stmts) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledCallsDisjoint
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (stmts := stmts)
          hsurface)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      (hdisjoint := hdisjoint)

/-- On helper-surface-closed statement lists, the new exact helper-aware list
bridge collapses to the old helper-free lifting path, but only needs the weaker
helper-free compiled compatibility witness. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListHelperFreeCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceStepInterface_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsteps :=
        stmtListHelperSurfaceStepInterface_of_helperSurfaceClosed
          (runtimeContract := runtimeContract)
          (spec := spec)
          (fields := fields)
          (scope := scope)
          (stmts := stmts)
          hsurface)
      (hlegacy := hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hinternal

/-- Combined fail-closed lifting bridge from the existing helper-free generic
statement library to the exact helper-aware compiled induction seam. The only
additional input beyond the already-proved helper-free cases is a
compiled-side legacy-compatibility witness for the statement list. -/
theorem stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_compiledLegacyCompatible
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hlegacy : StmtListCompiledLegacyCompatible fields scope stmts)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hinternal : runtimeContract.internalFunctions = []) :
    StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope stmts := by
  exact
    stmtListGenericWithHelpersAndHelperIR_of_core_helperSurfaceClosed_and_helperFreeCompiledLegacyCompatible
      (runtimeContract := runtimeContract)
      (spec := spec)
      (hgeneric := hgeneric)
      (hsurface := hsurface)
      (hlegacy :=
        stmtListHelperFreeCompiledLegacyCompatible_of_compiledLegacyCompatible hlegacy)
      (hnoEvents := hnoEvents)
      (hnoErrors := hnoErrors)
      hinternal


end Compiler.Proofs.IRGeneration
