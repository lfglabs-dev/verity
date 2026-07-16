import Compiler.Proofs.IRGeneration.GenericInduction.Helpers

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

/-- The selector-aware counterpart of `interpretInternalFunctionFuel` used at an
internal helper entry.  The source interpreter's public helper entry point uses
its default selector; an IR helper instead inherits the caller selector. -/
def internalHelperBodyInterpretation
    (spec : CompilationModel) (helperFuel : Nat) (callee : FunctionSpec)
    (initialWorld : Verity.ContractState) (selector : Nat) (args : List Nat) :
    SourceSemantics.InternalFunctionResult :=
  match SourceSemantics.bindInternalArgs callee.params args with
  | none => SourceSemantics.revertedInternalResult initialWorld
  | some bindings => internalHelperResultOfStmtResult initialWorld
      (internalHelperBodySourceResult spec callee initialWorld selector bindings helperFuel)

/-- Assumptions needed to apply the generic helper-body theorem at an internal
helper entry.  The generic theorem currently compiles an external-mode body;
`bodyCompile` records the actual `compileInternalFunction` body mode and
`compilationModesAgree` explicitly limits this bridge to helpers for which the
two compiled bodies coincide.  In particular, this is not a claim that
internal returns compile like external returns. -/
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
    spec.events spec.errors .calldata helper.rets true (internalHelperBodyScope callee helper)
    [] callee.body spec.functions = Except.ok helper.body
  compilationModesAgree :
    CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
      [] [] .calldata [] false (internalHelperBodyScope callee helper)
      [] callee.body spec.functions =
    CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
      spec.events spec.errors .calldata helper.rets true (internalHelperBodyScope callee helper)
      [] callee.body spec.functions
  scope : FunctionBody.scopeNamesPresent (internalHelperBodyScope callee helper) entryBindings
  exact : FunctionBody.bindingsExactlyMatchIRVarsOnScope
    (internalHelperBodyScope callee helper) entryBindings
    (prepareInternalCalleeState callerState helper args)
  bounded : FunctionBody.bindingsBounded entryBindings
  noEvents : spec.events = []
  noErrors : spec.errors = []
  runtime : FunctionBody.runtimeStateMatchesIR (SourceSemantics.effectiveFields spec)
    (internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
    (prepareInternalCalleeState callerState helper args)
  bodyExec : ∀ extraFuel,
    stmtResultMatchesIRExecWithInternals (SourceSemantics.effectiveFields spec)
      (internalHelperBodySourceResult spec callee initialWorld callerState.selector entryBindings helperFuel)
      (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel)

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
        (internalHelperBodySourceResult spec callee initialWorld callerState.selector entryBindings helperFuel)
        (internalHelperBodyIRExec runtimeContract helper callerState args extraFuel) ∧
      internalHelperBodyInterpretation spec helperFuel callee initialWorld callerState.selector args =
        internalHelperResultOfStmtResult initialWorld
          (internalHelperBodySourceResult spec callee initialWorld callerState.selector sourceBindings helperFuel) := by
  refine ⟨?_, ?_⟩
  · rcases exec_compileStmtList_generic_with_helpers_and_helper_ir_with_internals_sizeOf_extraFuel
        (runtimeContract := runtimeContract) (spec := spec)
        (fields := SourceSemantics.effectiveFields spec)
        (runtime := internalHelperBodyRuntime initialWorld callerState.selector entryBindings)
        (state := prepareInternalCalleeState callerState helper args)
        (scope := internalHelperBodyScope callee helper) (stmts := callee.body)
        helperFuel extraFuel hfuelPos ctx.generic ctx.scope ctx.exact ctx.bounded
        ctx.noEvents ctx.noErrors ctx.runtime with ⟨bodyIR, hcompile, hmatch⟩
    have hbody : bodyIR = helper.body := by
      apply Except.ok.inj
      calc
        Except.ok bodyIR =
            CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              [] [] .calldata [] false (internalHelperBodyScope callee helper)
              [] callee.body spec.functions := hcompile.symm
        _ = CompilationModel.compileStmtList (SourceSemantics.effectiveFields spec)
              spec.events spec.errors .calldata helper.rets true
              (internalHelperBodyScope callee helper) [] callee.body spec.functions :=
          ctx.compilationModesAgree
        _ = Except.ok helper.body := ctx.bodyCompile
    subst bodyIR
    exact hmatch
  · simp [internalHelperBodyInterpretation, ctx.bindArgs]

end Compiler.Proofs.IRGeneration
