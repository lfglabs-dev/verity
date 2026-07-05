import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ScopeValidation
import Compiler.CompilationModel.ValidationCalls
import Compiler.Proofs.IRGeneration.FunctionBody
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgeLemmas

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

/-- Source names visible to generic statement proofs must stay out of the
compiler scratch namespace used by compatibility temporaries. Internal
immutable storage fields may legally use other `__*` names. -/
def scopeAvoidsReservedCompilerPrefix (scope : List String) : Prop :=
  "__compat_value" ∉ scope ∧
  "__compat_packed" ∉ scope ∧
  "__compat_slot_word" ∉ scope ∧
  "__compat_slot_cleared" ∉ scope

/-- Single-step result relation used by the generic statement induction library.
Unlike `stmtResultMatchesIRExecExact`, this tracks the tail scope instead of
requiring exact bindings for every name in the runtime map. -/
def stmtStepMatchesIRExec
    (fields : List Field)
    (nextScope : List String) :
    SourceSemantics.StmtResult → IRExecResult → Prop
  | .continue runtime, .continue state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .stop runtime, .stop state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

/-- Helper-aware compiled-side counterpart of `stmtStepMatchesIRExec`. `leave`
is not accepted at the external statement-list boundary. -/
def stmtStepMatchesIRExecWithInternals
    (fields : List Field)
    (nextScope : List String) :
    SourceSemantics.StmtResult → IRExecResultWithInternals → Prop
  | .continue runtime, .continue state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state ∧
      FunctionBody.bindingsExactlyMatchIRVarsOnScope nextScope runtime.bindings state ∧
      FunctionBody.bindingsBounded runtime.bindings ∧
      FunctionBody.scopeNamesPresent nextScope runtime.bindings
  | .stop runtime, .stop state =>
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .return value runtime, .return value' state =>
      value = value' ∧
      FunctionBody.runtimeStateMatchesIR fields runtime state
  | .revert, .revert _ => True
  | _, _ => False

/-- Helper-aware compiled-side counterpart of
`FunctionBody.stmtResultMatchesIRExec`. `leave` is not accepted at the external
body boundary. -/
def stmtResultMatchesIRExecWithInternals
    (fields : List Field)
    (sourceResult : SourceSemantics.StmtResult) :
    IRExecResultWithInternals → Prop
  | .continue state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.continue state)
  | .return value state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.return value state)
  | .stop state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.stop state)
  | .revert state =>
      FunctionBody.stmtResultMatchesIRExec fields sourceResult (.revert state)
  | .leave _ => False

def externalIRExecResultToWithInternals : IRExecResult → IRExecResultWithInternals
  | .continue next => .continue next
  | .return value next => .return value next
  | .stop next => .stop next
  | .revert next => .revert next

theorem stmtStepMatchesIRExecWithInternals_of_stmtStepMatchesIRExec
    {fields : List Field}
    {nextScope : List String}
    {sourceResult : SourceSemantics.StmtResult}
    {irExec : IRExecResult}
    (hmatch : stmtStepMatchesIRExec fields nextScope sourceResult irExec) :
    stmtStepMatchesIRExecWithInternals fields nextScope sourceResult
      (externalIRExecResultToWithInternals irExec) := by
  cases sourceResult <;> cases irExec <;>
    simp [externalIRExecResultToWithInternals, stmtStepMatchesIRExec,
      stmtStepMatchesIRExecWithInternals] at hmatch ⊢ <;>
    exact hmatch

abbrev compiledIRWithInternalsCompat
    (runtimeContract : IRContract)
    (compiledIR : List YulStmt) : Prop :=
  ∀ state extraFuel,
    execIRStmtsWithInternals runtimeContract
        (compiledIR.length + extraFuel + 1) state compiledIR =
      externalIRExecResultToWithInternals
        (execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR)

/-- A compiled statement head that preserves the exact-state invariant needed to
continue generic statement-list induction on the remaining tail. -/
structure CompiledStmtStep
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmt fields runtime stmt = sourceResult ∧
        execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- Helper-aware single-step result relation for the future generic statement
induction path. The post-state shape is unchanged; only the source-side head step
is evaluated in the helper-aware semantics family. -/
structure CompiledStmtStepWithHelpers
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
      Except.ok compiledIR
  preserves :
    ∀ (runtime : SourceSemantics.RuntimeState)
      (state : IRState)
      (helperFuel : Nat)
      (extraFuel : Nat),
      FunctionBody.bindingsExactlyMatchIRVarsOnScope scope runtime.bindings state →
      FunctionBody.scopeNamesPresent scope runtime.bindings →
      FunctionBody.bindingsBounded runtime.bindings →
      FunctionBody.runtimeStateMatchesIR fields runtime state →
      sizeOf compiledIR - compiledIR.length ≤ extraFuel →
      ∃ sourceResult irExec,
        SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = sourceResult ∧
        execIRStmts (compiledIR.length + extraFuel + 1) state compiledIR = irExec ∧
        stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

/-- Exact helper-aware single-step interface for future helper-rich proofs: both
the source head step and the compiled head step run in the helper-aware
semantics families. This is the statement-level target needed for helper-rich
bodies because internal-call compilation can emit Yul forms such as `letMany`
that legacy `execIRStmts` rejects. -/
structure CompiledStmtStepWithHelpersAndHelperIR
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope [] stmt =
      Except.ok compiledIR
  preserves :
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
          fields (stmtNextScope scope stmt) sourceResult irExec

/-- Spec-functions-aware variant of `CompiledStmtStepWithHelpersAndHelperIR`.

The existing generic list induction still reconstructs statement-list
compilation through the default empty internal-function compiler argument.
Expression-position internal-helper payloads, however, compile through
`spec.functions`.  This witness records that exact compile shape while keeping
the same helper-aware source/IR preservation contract.  It is the narrow API
needed by helper-expression statement heads until the list-level induction gets
the corresponding internal-functions-parametric compile/scope lemmas. -/
structure CompiledStmtStepWithHelpersAndHelperIRWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field)
    (scope : List String)
    (stmt : Stmt)
    (compiledIR : List YulStmt) : Prop where
  compileOk :
    CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
        stmt spec.functions =
      Except.ok compiledIR
  preserves :
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
          fields (stmtNextScope scope stmt) sourceResult irExec

/-- Any legacy generic statement-step proof remains valid for the helper-aware
source semantics as long as the statement itself is helper-surface closed. This
lets the existing helper-free library discharge the unchanged cases while the
remaining work focuses only on genuinely helper-using statements. -/
theorem CompiledStmtStep.withHelpers_of_helperSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStep fields scope stmt compiledIR)
    (hnoEvents : spec.events = [])
    (hnoErrors : spec.errors = [])
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    CompiledStmtStepWithHelpers spec fields scope stmt compiledIR where
  compileOk := by simpa [hnoEvents, hnoErrors] using hstep.compileOk
  preserves := by
    intro runtime state helperFuel extraFuel hexact hscope hbounded hruntime hslack
    rcases hstep.preserves runtime state extraFuel
        hexact hscope hbounded hruntime hslack with
      ⟨sourceResult, irExec, hsource, hir, hmatch⟩
    refine ⟨sourceResult, irExec, ?_, hir, hmatch⟩
    simpa [hnoEvents, SourceSemantics.execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
      (spec := spec)
      (fields := fields)
      (fuel := helperFuel)
      (state := runtime)
      (stmt := stmt)
      hsurface] using hsource

/-- Events-agnostic sibling of
`CompiledStmtStep.withHelpers_of_helperSurfaceClosed`: instead of requiring the
whole spec to declare no events/errors, only the statement itself must stay off
the plain contract surface. This lets event-carrying specs reuse the helper-free
generic step library for every non-emit head. -/
theorem CompiledStmtStep.withHelpers_of_contractSurfaceClosed
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmt : Stmt}
    {compiledIR : List YulStmt}
    (hstep : CompiledStmtStep fields scope stmt compiledIR)
    (hcontractSurface : stmtTouchesUnsupportedContractSurface stmt = false)
    (hhelperSurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    CompiledStmtStepWithHelpers spec fields scope stmt compiledIR where
  compileOk := by
    rw [compileStmt_eventsErrorsAgnostic_of_contractSurfaceClosed hcontractSurface]
    exact hstep.compileOk
  preserves := by
    intro runtime state helperFuel extraFuel hexact hscope hbounded hruntime hslack
    rcases hstep.preserves runtime state extraFuel
        hexact hscope hbounded hruntime hslack with
      ⟨sourceResult, irExec, hsource, hir, hmatch⟩
    refine ⟨sourceResult, irExec, ?_, hir, hmatch⟩
    rw [SourceSemantics.execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
        spec fields helperFuel runtime stmt hhelperSurface,
      SourceSemantics.execStmtWithEvents_eq_execStmt_of_contractSurfaceClosed
        fields spec.events stmt hcontractSurface runtime]
    exact hsource

/-- Statement lists whose heads all admit a generic compiled-step proof. -/
inductive StmtListGenericCore (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericCore fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStep fields scope stmt compiledIR →
      StmtListGenericCore fields (stmtNextScope scope stmt) rest →
      StmtListGenericCore fields scope (stmt :: rest)

theorem compileStmtList_ok_of_stmtListGenericCore_early
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric : StmtListGenericCore fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields [] [] .calldata [] false inScopeNames [] stmts = Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope
        (scope2 := inScopeNames) ⟨_, hstep.compileOk⟩ with ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
          (by
            intro name hmem
            simp [stmtNextScope] at hmem
            rcases hmem with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        FunctionBody.compileStmtList_cons_ok_of_compileStmt_ok hhead htail⟩

/-- Internal-functions-parametric cons reconstruction for `compileStmtList`.
The existing `FunctionBody.compileStmtList_cons_eq_ok` defaults to `[]`; helper
expression compilation needs the same structural reconstruction under
`spec.functions`. -/
theorem compileStmtList_cons_eq_ok_with_internals
    (fields : List Field) (events : List EventDef) (errors : List ErrorDef)
    (dynamicSource : DynamicDataSource) (internalRetNames : List String)
    (isInternal : Bool) (inScopeNames : List String)
    (adtTypes : List AdtTypeDef) (stmt : Stmt) (rest : List Stmt)
    (internalFunctions : List FunctionSpec)
    (headIR tailIR : List YulStmt)
    (hhead :
      CompilationModel.compileStmt fields events errors dynamicSource
        internalRetNames isInternal inScopeNames adtTypes stmt internalFunctions =
          Except.ok headIR)
    (htail :
      CompilationModel.compileStmtList fields events errors dynamicSource
        internalRetNames isInternal (collectStmtNames stmt ++ inScopeNames) adtTypes
          rest internalFunctions =
          Except.ok tailIR) :
    CompilationModel.compileStmtList fields events errors dynamicSource
      internalRetNames isInternal inScopeNames adtTypes (stmt :: rest) internalFunctions =
        Except.ok (headIR ++ tailIR) := by
  unfold CompilationModel.compileStmtList
  unfold CompilationModel.compileStmtListWithFork
  simp [bind, Except.bind, Pure.pure, Except.pure,
    FunctionBody.compileStmtWithFork_cancun_eq_compileStmt,
    FunctionBody.compileStmtListWithFork_cancun_eq_compileStmtList,
    hhead, htail]

/-- Weaker source-side reuse witness for the future helper-rich induction path:
only helper-surface-closed heads must come with the existing helper-free
generic step proof. Helper-surface-positive heads can instead be discharged by a
dedicated exact helper-aware step proof at the point where the exact seam is
assembled. -/
inductive StmtListHelperFreeStepInterface
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeStepInterface fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∃ compiledIR,
          CompiledStmtStep fields scope stmt compiledIR) →
      StmtListHelperFreeStepInterface fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeStepInterface fields scope (stmt :: rest)

/-- Scalar-event variant of the helper-free source-step interface. Event heads
are discharged by `StmtListEventSurfaceStepInterface`, so helper-free compiled
steps are required only for non-event heads. -/
inductive StmtListHelperFreeNonEventStepInterface
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeNonEventStepInterface fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        stmtTouchesEventSurface stmt = false →
        ∃ compiledIR,
          CompiledStmtStep fields scope stmt compiledIR) →
      StmtListHelperFreeNonEventStepInterface fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeNonEventStepInterface fields scope (stmt :: rest)

/-- Exact step interface for direct event-emission heads. Non-event heads are
discharged elsewhere; `.emit` heads must provide a helper-aware compiled step
because event compilation depends on `spec.events`. -/
inductive StmtListEventSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListEventSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesEventSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListEventSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListEventSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Statement lists whose heads all admit a helper-aware generic compiled-step
proof. This is the exact induction-level seam needed to consume helper-summary
soundness and decreasing-rank evidence without reusing the helper-free
`SupportedStmtList` witness. -/
inductive StmtListGenericWithHelpers
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericWithHelpers spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStepWithHelpers spec fields scope stmt compiledIR →
      StmtListGenericWithHelpers spec fields (stmtNextScope scope stmt) rest →
      StmtListGenericWithHelpers spec fields scope (stmt :: rest)

/-- Exact helper-aware statement-list induction seam: both source execution and
compiled execution already target the helper-aware semantics. This is the list
level interface needed once helper-rich statements enter the theorem domain. -/
inductive StmtListGenericWithHelpersAndHelperIR
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStepWithHelpersAndHelperIR
        runtimeContract spec fields scope stmt compiledIR →
      StmtListGenericWithHelpersAndHelperIR
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListGenericWithHelpersAndHelperIR runtimeContract spec fields scope (stmt :: rest)

/-- Spec-functions-aware sibling of
`StmtListGenericWithHelpersAndHelperIR`.  It is deliberately narrow: it records
the same helper-aware source/IR preservation witness, but its compile facts are
for `compileStmt ... stmt spec.functions`.  The arbitrary-scope reconstruction
API is still blocked on a parametric version of
`FunctionBody.compileStmt_ok_any_scope_with_surface`; this exact-scope seam is
enough for callers that thread the compiler scope structurally. -/
inductive StmtListGenericWithHelpersAndHelperIRWithInternals
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {compiledIR : List YulStmt} {rest : List Stmt} :
      CompiledStmtStepWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmt compiledIR →
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope (stmt :: rest)

/-- Exact-scope compile reconstruction for the spec-functions-aware helper IR
list seam. -/
theorem compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIRWithInternals_exact
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope : List String}
    {stmts : List Stmt}
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmts) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false scope [] stmts spec.functions =
          Except.ok bodyIR := by
  induction hgeneric with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | @cons scope stmt compiledIR rest hstep _hrest ih =>
      rcases ih with ⟨tailIR, htail⟩
      exact ⟨compiledIR ++ tailIR,
        compileStmtList_cons_eq_ok_with_internals
          fields spec.events spec.errors .calldata [] false scope [] stmt rest
          spec.functions compiledIR tailIR hstep.compileOk htail⟩

/-- Scope-lifted compile reconstruction for the spec-functions-aware helper IR
list seam.

This is the `spec.functions` counterpart of
`compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIR`: each exact head
compile is first retargeted to the caller-provided scope with the
internal-functions-parametric scope theorem, then the list is reconstructed
under that same helper world. -/
theorem compileStmtList_ok_of_stmtListGenericWithHelpersAndHelperIRWithInternals
    {runtimeContract : IRContract}
    {spec : CompilationModel}
    {fields : List Field}
    {scope inScopeNames : List String}
    {stmts : List Stmt}
    (hgeneric :
      StmtListGenericWithHelpersAndHelperIRWithInternals
        runtimeContract spec fields scope stmts)
    (hincluded : FunctionBody.scopeNamesIncluded scope inScopeNames) :
    ∃ bodyIR,
      CompilationModel.compileStmtList
        fields spec.events spec.errors .calldata [] false inScopeNames [] stmts spec.functions =
          Except.ok bodyIR := by
  induction hgeneric generalizing inScopeNames with
  | nil =>
      exact ⟨[], by
        simp [CompilationModel.compileStmtList, CompilationModel.compileStmtListWithFork,
          Pure.pure, Except.pure]⟩
  | cons hstep _hrest ih =>
      rcases FunctionBody.compileStmt_ok_any_scope_with_surface_with_internals
          (scope2 := inScopeNames)
          (internalFunctions := spec.functions)
          ⟨_, hstep.compileOk⟩ with
        ⟨headIR, hhead⟩
      rcases ih (inScopeNames := collectStmtNames _ ++ inScopeNames)
          (by
            intro name hmem
            simp [stmtNextScope] at hmem
            rcases hmem with h | h
            · exact List.mem_append_left _ h
            · exact List.mem_append_right _ (hincluded name h))
        with ⟨tailIR, htail⟩
      exact ⟨headIR ++ tailIR,
        compileStmtList_cons_eq_ok_with_internals
          fields spec.events spec.errors .calldata [] false inScopeNames [] _ _
          spec.functions headIR tailIR hhead htail⟩

/-- Compiled-side compatibility witness for lifting existing helper-free generic
statement proofs into the exact helper-aware compiled induction seam. This
records that each compiled head stays inside the already-closed
legacy-compatible external Yul subset, without coupling the witness to any
particular statement-step proof object. -/
inductive StmtListCompiledLegacyCompatible
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListCompiledLegacyCompatible fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (∀ compiledIR,
        CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
          Except.ok compiledIR →
          LegacyCompatibleExternalStmtList compiledIR) →
      StmtListCompiledLegacyCompatible fields (stmtNextScope scope stmt) rest →
      StmtListCompiledLegacyCompatible fields scope (stmt :: rest)

/-- Weaker compiled-side compatibility witness for the exact helper-aware
induction seam: only helper-surface-closed statement heads must stay inside the
legacy-compatible external Yul subset. Helper-positive heads can instead be
discharged by dedicated exact helper-aware step proofs. -/
inductive StmtListHelperFreeCompiledLegacyCompatible
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeCompiledLegacyCompatible fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∀ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
            Except.ok compiledIR →
            LegacyCompatibleExternalStmtList compiledIR) →
      StmtListHelperFreeCompiledLegacyCompatible fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeCompiledLegacyCompatible fields scope (stmt :: rest)

/-- Disjoint-based compiled-side compatibility: helper-surface-closed statement
heads produce compiled IR that is disjoint from the runtime contract's internal
function table.  Unlike `StmtListHelperFreeCompiledLegacyCompatible` this does
**not** require `runtimeContract.internalFunctions = []` downstream. -/
inductive StmtListHelperFreeCompiledCallsDisjoint
    (runtimeContract : IRContract)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = false →
        ∀ compiledIR,
          CompilationModel.compileStmt fields [] [] .calldata [] false scope [] stmt =
            Except.ok compiledIR →
            YulStmtListCallsDisjointFromInternalTable runtimeContract compiledIR) →
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields (stmtNextScope scope stmt) rest →
      StmtListHelperFreeCompiledCallsDisjoint runtimeContract fields scope (stmt :: rest)

/-- List-local exact step interface for the genuinely new helper-surface
statement heads. Helper-free heads remain reusable through the existing
helper-free generic step library plus the helper-free compiled compatibility
witness. -/
inductive StmtListHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for heads that genuinely execute internal helpers under
the helper-aware semantics. This is the new proof work that should consume
helper-summary/rank evidence. -/
inductive StmtListInternalHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListInternalHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListInternalHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for direct statement-position internal-helper heads.
These are the cases that should consume the statement-level helper-summary
soundness lemmas from `SourceSemantics.lean` directly. -/
inductive StmtListDirectInternalHelperCallStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperCallSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperCallStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperCallStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for direct statement-position helper-return binding
heads. These are the cases that should consume the `Stmt.internalCallAssign`
summary shape directly instead of sharing one bucket with void helper calls. -/
inductive StmtListDirectInternalHelperAssignStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperAssignSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperAssignStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperAssignStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Coarser direct statement-position helper interface retained as the assembly
point for the two direct helper proof shapes above. -/
inductive StmtListDirectInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesDirectInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListDirectInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListDirectInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for heads whose internal-helper work appears only in
expression position at the current statement head. These are the cases that
should consume the expression-level summary-soundness/world-preservation lemmas
directly. -/
inductive StmtListExprInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesExprInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListExprInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListExprInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Exact step interface for structural heads whose helper burden is recursive
transport through nested bodies (`ite` / `forEach`) rather than direct helper
summary consumption at the head itself. -/
inductive StmtListStructuralInternalHelperStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesStructuralInternalHelperSurface stmt = true →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListStructuralInternalHelperStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListStructuralInternalHelperStepInterface runtimeContract spec fields scope (stmt :: rest)

/-- Residual exact-step interface for heads that still fall on the coarse old
helper surface but do not actually execute internal helpers. Splitting these
out prevents future helper-summary work from having to discharge unrelated
non-helper proof gaps such as broader expression/core cases. -/
inductive StmtListResidualHelperSurfaceStepInterface
    (runtimeContract : IRContract)
    (spec : CompilationModel)
    (fields : List Field) : List String → List Stmt → Prop where
  | nil {scope : List String} :
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope []
  | cons {scope : List String} {stmt : Stmt} {rest : List Stmt} :
      (stmtTouchesUnsupportedHelperSurface stmt = true →
        stmtTouchesInternalHelperSurface stmt = false →
        ∃ compiledIR,
          CompiledStmtStepWithHelpersAndHelperIR
            runtimeContract spec fields scope stmt compiledIR) →
      StmtListResidualHelperSurfaceStepInterface
        runtimeContract spec fields (stmtNextScope scope stmt) rest →
      StmtListResidualHelperSurfaceStepInterface runtimeContract spec fields scope (stmt :: rest)


end Compiler.Proofs.IRGeneration
