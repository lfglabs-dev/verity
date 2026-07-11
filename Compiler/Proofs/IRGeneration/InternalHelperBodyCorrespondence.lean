import Compiler.Proofs.IRGeneration.GenericInduction.Helpers

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

def internalHelperBodyScope (callee : FunctionSpec) (helper : IRInternalFunctionDef) :
    List String :=
  CompilationModel.internalFunctionYulParamNames callee.params ++ helper.rets

def internalHelperBodyRuntime
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat)) :
    SourceSemantics.RuntimeState :=
  { world := initialWorld, bindings := bindings }

def internalHelperBodySourceResult
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (bindings : List (String × Nat))
    (helperFuel : Nat) : SourceSemantics.StmtResult :=
  SourceSemantics.execStmtListWithHelpers spec (SourceSemantics.effectiveFields spec)
    helperFuel (internalHelperBodyRuntime initialWorld bindings) callee.body

noncomputable def internalHelperBodyIRExec
    (runtimeContract : IRContract) (helper : IRInternalFunctionDef)
    (callerState : IRState) (args : List Nat) (extraFuel : Nat) :
    IRExecResultWithInternals :=
  execIRStmtsWithInternals runtimeContract (sizeOf helper.body + extraFuel + 1)
    (prepareInternalCalleeState callerState helper args) helper.body

def internalHelperResultOfStmtResult
    (initialWorld : Verity.ContractState) : SourceSemantics.StmtResult →
    SourceSemantics.InternalFunctionResult
  | .continue finalState => SourceSemantics.successInternalResult finalState.world none
  | .stop finalState => SourceSemantics.successInternalResult finalState.world none
  | .return value finalState => SourceSemantics.successInternalResult finalState.world (some value)
  | .revert => SourceSemantics.revertedInternalResult initialWorld

/-- Assumptions needed to apply the generic helper-body theorem at an internal
helper entry.  `bodyBindings` is the remaining ret-slot/source-binding seam:
the generic theorem needs bindings for compiled return slots, while
`interpretInternalFunctionFuel` starts from raw `bindInternalArgs` bindings. -/
structure InternalHelperBodyExecContext
    (runtimeContract : IRContract) (spec : CompilationModel)
    (callee : FunctionSpec) (helper : IRInternalFunctionDef)
    (callerState : IRState) (initialWorld : Verity.ContractState)
    (args : List Nat) (sourceBindings entryBindings : List (String × Nat))
    (helperFuel : Nat) : Prop where
  bindArgs : SourceSemantics.bindInternalArgs callee.params args = some sourceBindings
  helperParams : helper.params = CompilationModel.internalFunctionYulParamNames callee.params
  generic : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
    (SourceSemantics.effectiveFields spec) (internalHelperBodyScope callee helper) callee.body
  bodyCompile : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
    [] [] .calldata [] false (internalHelperBodyScope callee helper)
    [] callee.body spec.functions = Except.ok helper.body
  bodyBindings : internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel =
    internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel
  scope : FunctionBody.scopeNamesPresent (internalHelperBodyScope callee helper) entryBindings
  exact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
    (internalHelperBodyScope callee helper) entryBindings
    (prepareInternalCalleeState callerState helper args)
  bounded : FunctionBody.bindingsBounded entryBindings
  noEvents : spec.events = []
  noErrors : spec.errors = []
  runtime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields spec)
    (internalHelperBodyRuntime initialWorld entryBindings)
    (prepareInternalCalleeState callerState helper args)

/-- Helper-entry/body correspondence for the N1a internal-helper path. -/
theorem internal_helper_body_exec_matches_of_bindInternalArgs_and_generic
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {args : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld args sourceBindings entryBindings helperFuel) :
    stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) ∧
      SourceSemantics.interpretInternalFunctionFuel spec helperFuel callee initialWorld args =
        internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld sourceBindings helperFuel) := by
  have hgeneric' : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
      (SourceSemantics.effectiveFields spec) (helper.params ++ helper.rets) callee.body := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.generic
  have hbodyCompile' : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
      [] [] .calldata [] false (helper.params ++ helper.rets)
      [] callee.body spec.functions = Except.ok helper.body := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.bodyCompile
  have hscope' : FunctionBody.scopeNamesPresent (helper.params ++ helper.rets) entryBindings := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.scope
  have hexact' : FunctionBody.bindingsExactlyMatchIRVarsOnScope
      (helper.params ++ helper.rets) entryBindings
      (prepareInternalCalleeState callerState helper args) := by
    simpa [internalHelperBodyScope, ctx.helperParams] using ctx.exact
  rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel
      (runtime := internalHelperBodyRuntime initialWorld entryBindings)
      (state := prepareInternalCalleeState callerState helper args)
      (scope := helper.params ++ helper.rets) (stmts := callee.body)
      (helperFuel := helperFuel) (extraFuel := extraFuel)
      hfuelPos hgeneric' hscope' hexact' ctx.bounded ctx.noEvents ctx.noErrors ctx.runtime with
    ⟨bodyIR, hcompile, hmatch⟩
  have hbodyEq : bodyIR = helper.body := by
    rw [hbodyCompile'] at hcompile
    injection hcompile with hbodyEq
    exact hbodyEq.symm
  subst bodyIR
  refine ⟨?_, ?_⟩
  · have hmatch' : stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld entryBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) := by
      simpa [internalHelperBodySourceResult, internalHelperBodyIRExec] using hmatch
    rw [ctx.bodyBindings] at hmatch'
    exact hmatch'
  · simp [internalHelperBodySourceResult, internalHelperResultOfStmtResult,
      SourceSemantics.interpretInternalFunctionFuel, ctx.bindArgs]
    rfl

end Compiler.Proofs.IRGeneration
