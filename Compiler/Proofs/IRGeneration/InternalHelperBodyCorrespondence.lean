import Compiler.Proofs.IRGeneration.GenericInduction.Helpers
import Compiler.Proofs.IRGeneration.HelperBodyBridge

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Yul

def internalHelperBodyScope (callee : FunctionSpec) (helper : IRInternalFunctionDef) :
    List String :=
  CompilationModel.internalFunctionYulParamNames callee.params ++ helper.rets

def internalHelperBodyRuntime
    (initialWorld : Verity.ContractState) (selector : Nat) (bindings : List (String × Nat)) :
    SourceSemantics.RuntimeState :=
  { world := initialWorld, selector := selector, bindings := bindings }

def internalHelperBodySourceResult
    (spec : CompilationModel) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat) (bindings : List (String × Nat))
    (helperFuel : Nat) : SourceSemantics.StmtResult :=
  SourceSemantics.execStmtListWithHelpers spec (SourceSemantics.effectiveFields spec)
    helperFuel (internalHelperBodyRuntime initialWorld selector bindings) callee.body

noncomputable def internalHelperBodyIRExec
    (runtimeContract : IRContract) (helper : IRInternalFunctionDef)
    (callerState : IRState) (irArgs : List Nat) (extraFuel : Nat) :
    IRExecResultWithInternals :=
  execIRStmtsWithInternals runtimeContract (sizeOf helper.body + extraFuel + 1)
    (prepareInternalCalleeState callerState helper irArgs) helper.body

def internalHelperResultOfStmtResult
    (initialWorld : Verity.ContractState) : SourceSemantics.StmtResult →
    SourceSemantics.InternalFunctionResult
  | .continue finalState => SourceSemantics.successInternalResult finalState.world none
  | .stop finalState => SourceSemantics.successInternalResult finalState.world none
  | .return value finalState => SourceSemantics.successInternalResult finalState.world (some value)
  | .revert => SourceSemantics.revertedInternalResult initialWorld

/-- The selector-aware counterpart of `interpretInternalFunctionFuel` used at an
internal helper entry.  The source interpreter's public helper entry point uses
its default selector; an IR helper instead inherits the caller selector. -/
def internalHelperBodyInterpretation
    (spec : CompilationModel) (helperFuel : Nat) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat) (logicalArgs : List Nat) :
    SourceSemantics.InternalFunctionResult :=
  match SourceSemantics.bindInternalArgs callee.params logicalArgs with
  | none => SourceSemantics.revertedInternalResult initialWorld
  | some bindings => internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld selector bindings helperFuel)

/-- Assumptions needed to apply the generic helper-body theorem at an internal
helper entry. The available generic theorem compiles an external-mode body, so
this bridge is explicitly limited to return-family-free bodies, for which the
existing shape theorem derives its equality with the internal-mode body. -/
structure InternalHelperBodyExecContext
    (runtimeContract : IRContract) (spec : CompilationModel)
    (callee : FunctionSpec) (helper : IRInternalFunctionDef)
    (callerState : IRState) (initialWorld : Verity.ContractState)
    (logicalArgs irArgs : List Nat) (sourceBindings entryBindings : List (String × Nat))
    (helperFuel : Nat) : Prop where
  /-- Source arguments have one value per source parameter, whereas `irArgs`
  has one value per lowered Yul parameter. -/
  bindArgs : SourceSemantics.bindInternalArgs callee.params logicalArgs = some sourceBindings
  helperParams : helper.params = CompilationModel.internalFunctionYulParamNames callee.params
  generic : StmtListGenericWithHelpersAndHelperIRWithInternals runtimeContract spec
    (SourceSemantics.effectiveFields spec) (internalHelperBodyScope callee helper) callee.body
  bodyCompile : CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
    spec.events spec.errors .calldata helper.rets true (internalHelperBodyScope callee helper)
    [] callee.body spec.functions = Except.ok helper.body
  returnFree : stmtListUsesReturnFamily callee.body = false
  /-- This bridge returns an internal-function result, so bodies that can
  propagate `.stop` to the IR caller are excluded at this boundary. -/
  noStop : stmtListUsesStop callee.body = false
  /-- The source bindings obtained from logical arguments and the bindings at
  the prepared IR entry execute this body identically. -/
  bodyBindings :
    internalHelperBodySourceResult spec callee initialWorld callerState.selector entryBindings
      helperFuel =
    internalHelperBodySourceResult spec callee initialWorld callerState.selector sourceBindings
      helperFuel
  scope : FunctionBody.scopeNamesPresent (internalHelperBodyScope callee helper) entryBindings
  exact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
    (internalHelperBodyScope callee helper) entryBindings
    (prepareInternalCalleeState callerState helper irArgs)
  bounded : FunctionBody.bindingsBounded entryBindings
  runtime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields spec)
    (internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
    (prepareInternalCalleeState callerState helper irArgs)

/-- Helper-entry/body correspondence for the N1a internal-helper path. -/
theorem internal_helper_body_exec_matches_of_bindInternalArgs_and_generic
    {runtimeContract : IRContract} {spec : CompilationModel}
    {callee : FunctionSpec} {helper : IRInternalFunctionDef}
    {callerState : IRState} {initialWorld : Verity.ContractState}
    {logicalArgs irArgs : List Nat} {sourceBindings entryBindings : List (String × Nat)}
    (helperFuel extraFuel : Nat) (hfuelPos : 0 < helperFuel)
    (ctx : InternalHelperBodyExecContext runtimeContract spec callee helper
      callerState initialWorld logicalArgs irArgs sourceBindings entryBindings helperFuel) :
    stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
        (internalHelperBodySourceResult spec callee initialWorld callerState.selector sourceBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState irArgs extraFuel) ∧
      internalHelperBodyInterpretation spec helperFuel callee initialWorld callerState.selector logicalArgs =
        internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld callerState.selector sourceBindings helperFuel) := by
  refine ⟨?_, ?_⟩
  · rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel_step
        (runtimeContract := runtimeContract) (spec := spec)
        (fields := SourceSemantics.effectiveFields spec)
        (runtime := internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
        (state := prepareInternalCalleeState callerState helper irArgs)
        (scope := internalHelperBodyScope callee helper) (stmts := callee.body)
        helperFuel extraFuel hfuelPos ctx.generic ctx.scope ctx.exact ctx.bounded
        ctx.runtime with ⟨bodyIR, hcompile, hstep⟩
    have hmatch :=
      stmtStepMatchesIRExecWithInternals_implies_stmtResultMatchesIRExecWithInternals hstep
    have hmode :=
      compileStmtListWithFork_internal_shape_irrelevant_of_returnFree
        (SourceSemantics.effectiveFields spec) spec.events spec.errors .calldata
        helper.rets true (internalHelperBodyScope callee helper) []
        Verity.Core.Intrinsics.HardFork.cancun callee.body spec.functions ctx.returnFree
    have hbody : bodyIR = helper.body := by
      apply Except.ok.inj
      calc
        Except.ok bodyIR =
            CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              spec.events spec.errors .calldata [] false (internalHelperBodyScope callee helper)
              [] callee.body spec.functions := hcompile.symm
        _ = CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              spec.events spec.errors .calldata helper.rets true
              (internalHelperBodyScope callee helper) [] callee.body spec.functions := by
          simpa only [CompilationModel.compileStmtList] using hmode.symm
        _ = Except.ok helper.body := ctx.bodyCompile
    subst bodyIR
    rw [← ctx.bodyBindings]
    simpa [internalHelperBodySourceResult, internalHelperBodyIRExec] using hmatch
  · simp [internalHelperBodyInterpretation, ctx.bindArgs]

end Compiler.Proofs.IRGeneration
