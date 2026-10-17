import Compiler.Proofs.IRGeneration.GenericInduction.SupportedEventOrdinary
import Compiler.Proofs.IRGeneration.PublicResultBridge
import Compiler.Proofs.IRGeneration.FunctionValidationBounds
import Compiler.Proofs.IRGeneration.GenericInduction.SupportedOrdinary
import Compiler.Proofs.IRGeneration.SourceErrorDeclarations
import Compiler.Proofs.IRGeneration.GenericInduction.OrdinaryTrace
import Compiler.Proofs.IRGeneration.GenericInduction.ContextualBody
import Compiler.Proofs.IRGeneration.GenericInduction.Storage

namespace SolidityImportSmoke.GenericReturndataChecks
open Compiler.CompilationModel Compiler.Proofs.IRGeneration Compiler.Yul

/-- A different opcode frame cannot enter the compiled-step proof interface. -/
example (fields : List Field) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (different : runtime.executionContext ≠ state.executionContext) :
    ¬ FunctionBody.runtimeStateMatchesIR fields runtime state := by
  intro admitted
  exact different (FunctionBody.runtimeStateMatchesIR_executionContext admitted)

/-- The actual retained size, not a truncated size word, controls admission. -/
example (fields : List Field) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (tooLarge : Verity.Core.Uint256.modulus ≤ 32 * state.returndata.length) :
    ¬ FunctionBody.runtimeStateMatchesIR fields runtime state := by
  intro admitted
  exact Nat.not_lt_of_ge tooLarge
    (FunctionBody.runtimeStateMatchesIR_returndata_extent admitted)

/-- Existing admission suffices for exact bubbling, for arbitrary payload words. -/
example (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (extraFuel : Nat)
    (admitted : FunctionBody.runtimeStateMatchesIR fields runtime state)
    (slack : sizeOf PhysicalReturndataExecution.body -
      PhysicalReturndataExecution.body.length ≤ extraFuel) :
    ∃ sourceResult irExec,
      SourceSemantics.execStmt fields runtime .revertReturndata = sourceResult ∧
      execIRStmts (PhysicalReturndataExecution.body.length + extraFuel + 1)
        state PhysicalReturndataExecution.body = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope .revertReturndata)
        sourceResult irExec :=
  compiled_revertReturndata_exact_bytes runtime state extraFuel admitted
    (FunctionBody.runtimeStateMatchesIR_returndata_extent admitted) slack

/-- Both typed result classes remain distinct at the operational step boundary. -/
example (fields : List Field) (scope : List String) (message : String) (state : IRState) :
    ¬ stmtStepMatchesIRExec fields scope (.interpretationError message) (.revert state) := by
  simp [stmtStepMatchesIRExec]

example (fields : List Field) (scope : List String) (runtime : SourceSemantics.RuntimeState)
    (state : IRState) :
    ¬ stmtStepMatchesIRExec fields scope (.exceptional runtime) (.revert state) := by
  simp [stmtStepMatchesIRExec]

/-- Operational refusal agreement cannot be mistaken for a public EVM proof. -/
example (fields : List Field) (message : String) (rollback : IRState)
    (spec : CompilationModel) (initial : Verity.ContractState) :
    stmtOutcomeMatchesIRExec fields (.interpretationError message) (.interpretationError message) ∧
      ¬ FunctionBody.sourceResultMatchesIRResult
        (FunctionBody.stmtResultToSourceResult spec initial (.interpretationError message))
        (FunctionBody.irResultOfExecResult rollback (.interpretationError message)) :=
  operational_refusal_not_certified fields message rollback spec initial

/-- The bridge preserves the existing certificate exactly; matching refusals
and exceptional states cannot acquire an ordinary-halt certificate. -/
example (fields : List Field) (source : SourceSemantics.StmtResult) (ir : IRExecResult) :
    FunctionBody.stmtResultMatchesIRExec fields source ir ↔
      stmtOutcomeMatchesIRExec fields source ir ∧ stmtOutcomeIsOrdinary source :=
  stmtOutcomeMatchesIRExec_certified_iff fields source ir

example (fields : List Field) (source : SourceSemantics.StmtResult)
    (ir : IRExecResultWithInternals) :
    stmtResultMatchesIRExecWithInternals fields source ir ↔
      stmtOutcomeMatchesIRExecWithInternals fields source ir ∧ stmtOutcomeIsOrdinary source :=
  stmtOutcomeMatchesIRExecWithInternals_certified_iff fields source ir

example (fields : List Field) (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (aligned : FunctionBody.runtimeStateMatchesIR fields runtime state) :
    stmtOutcomeMatchesIRExec fields (.exceptional runtime) (.exceptional state) ∧
      ¬ FunctionBody.stmtResultMatchesIRExec fields (.exceptional runtime) (.exceptional state) := by
  exact ⟨aligned, by simp [FunctionBody.stmtResultMatchesIRExec]⟩

/-- In-bounds admission composes at the actual post-copy state. -/
example {fields : List Field} {runtime : SourceSemantics.RuntimeState}
    {destination source size : Expr} {dst src extent : Nat}
    (hd : SourceSemantics.evalExpr fields runtime destination = some dst)
    (hs : SourceSemantics.evalExpr fields runtime source = some src)
    (hz : SourceSemantics.evalExpr fields runtime size = some extent)
    (inside : src % Verity.Core.Uint256.modulus + extent % Verity.Core.Uint256.modulus ≤
      32 * runtime.world.returndata.length) :
    OrdinarySourceTrace fields runtime [.returndataCopy destination source size, .stop] :=
  ordinarySourceTrace_returndataCopy hd hs hz inside
    (ordinarySourceTrace_stop _ _ [])

/-- A zero-length copy still checks its source offset. This concrete near miss
cannot enter ordinary certification when the current return buffer is empty. -/
example (runtime : SourceSemantics.RuntimeState)
    (empty : runtime.world.returndata = []) (missing : runtime.executionContext = none) :
    ¬ OrdinarySourceTrace [] runtime
      [.returndataCopy (.literal 0) (.literal 1) (.literal 0)] := by
  apply no_ordinarySourceTrace_returndataCopy_missing_context
    (dst := 0) (src := 1) (extent := 0) rfl rfl rfl missing
  rw [empty]
  decide

/-- Actual helper steps, including a terminal STOP, construct the trace. -/
example (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (runtime : SourceSemantics.RuntimeState) :
    OrdinaryHelperTrace spec fields fuel runtime [.stop, .returndataCopy (.literal 0) (.literal 1) (.literal 0)] := by
  exact OrdinaryHelperTrace.stopped (final := runtime) (by simp [SourceSemantics.execStmtWithHelpers])

/-- The unreachable suffix above cannot be admitted when executed on its own. -/
example (spec : CompilationModel) (fuel : Nat) (runtime : SourceSemantics.RuntimeState)
    (empty : runtime.world.returndata = []) (missing : runtime.executionContext = none) :
    ¬ OrdinaryHelperTrace spec [] fuel runtime
      [.returndataCopy (.literal 0) (.literal 1) (.literal 0)] := by
  intro trace
  have ordinary := trace.outcome_is_ordinary
  simp [SourceSemantics.execStmtListWithHelpers, SourceSemantics.execStmtWithHelpers,
    SourceSemantics.evalExprWithHelpers, SourceSemantics.execReturndataCopy,
    Verity.Core.Model.ReturndataCopy.run, empty, missing, stmtOutcomeIsOrdinary] at ordinary

/-- Supported core admission is derived for the real execution, not assumed. -/
example {scope : List String} {stmts : List Stmt}
    (supported : FunctionBody.StmtListCompileCore scope stmts)
    (fields : List Field) (runtime : SourceSemantics.RuntimeState) :
    OrdinarySourceTrace fields runtime stmts :=
  .of_ordinary_outcome (compile_core_ordinary supported fields runtime)

/-- The whole supported grammar has an ordinary execution trace. -/
example {fields : List Field} {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts)
    (runtime : SourceSemantics.RuntimeState) : OrdinarySourceTrace fields runtime stmts :=
  .of_ordinary_outcome (supported.outcome_is_ordinary runtime)

/-- The actual catalog-aware trace is derived even with event definitions. -/
example {fields : List Field} {scope : List String} {stmts : List Stmt}
    (supported : SupportedStmtList fields scope stmts) (spec : CompilationModel)
    (fuel : Nat) (runtime : SourceSemantics.RuntimeState) :
    OrdinaryHelperTrace spec fields fuel runtime stmts :=
  supported.ordinary_helper_trace_with_events spec fuel runtime supported.helperSurfaceClosed

/-- Actual exceptional internal executions retain the model's error table. -/
example (spec : CompilationModel) (fuel : Nat) (fn : FunctionSpec)
    (world : Verity.ContractState) (args : List Nat)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome) (cursor : Nat)
    (context : Option Verity.Core.Model.ExecutionContext) (terminal : SourceSemantics.RuntimeState)
    (executed : (SourceSemantics.interpretInternalFunctionFuel spec fuel fn world args oracle cursor context).exceptionalState = some terminal) :
    terminal.errors = spec.errors :=
  SourceErrorDeclarations.internal_exception_errors spec fuel fn world args oracle cursor context terminal executed

/-- Physical payload admission includes empty and multiword UTF-8 messages. -/
example : requirePayloadFitsWord "" = true := by unfold requirePayloadFitsWord; decide +kernel
example : requirePayloadFitsWord "é🙂\x00" = true := by unfold requirePayloadFitsWord; decide +kernel
example : requirePayloadFitsWord (String.ofList (List.replicate 65 'x')) = true := by unfold requirePayloadFitsWord; decide +kernel

/-- An oversized nested message is rejected, even in a loop nested in a branch.
This quantified regression covers the unmaterializable EVM-size boundary. -/
example (message : String) (oversized : requirePayloadFitsWord message = false) :
    validateRequirePayloads "nested" [.ite (.literal 1)
      [.forEach "i" (.literal 1) [.require (.literal 0) message]] []] =
      .error "Compilation error: nested contains a require message whose ABI Error(string) payload exceeds the EVM word address space." := by
  have loopOccurs : FunctionBody.RequireMessageOccurs
      [.forEach "i" (.literal 1) [.require (.literal 0) message]] message :=
    .child (body := [.require (.literal 0) message]) (by simp [Stmt.childLists]) .here
  have occurs : FunctionBody.RequireMessageOccurs
      [.ite (.literal 1) [.forEach "i" (.literal 1) [.require (.literal 0) message]] []] message :=
    .child (body := [.forEach "i" (.literal 1) [.require (.literal 0) message]])
      (by simp [Stmt.childLists]) loopOccurs
  simp only [validateRequirePayloads, FunctionBody.requireMessageOccurs_overflow occurs oversized,
    ↓reduceIte]
  apply congrArg Except.error
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  decide +kernel

/-- Production validation, rather than a new proof assumption, supplies bounds. -/
example (fn : FunctionSpec) (validated : validateFunctionSpec fn = .ok ()) :
    FunctionBody.requirePayloadsFit fn.body :=
  requirePayloadsFit_of_validateFunctionSpec fn validated

/-- Constructors use the same production message-bound check as functions. -/
example (ctor : ConstructorSpec)
    (validated : validateConstructorSpec (some ctor) = .ok ()) :
    FunctionBody.requirePayloadsFit ctor.body :=
  requirePayloadsFit_of_validateConstructorSpec ctor validated

example : validateConstructorSpec none = .ok () := rfl

/-- The production constructor wrapper rejects every detected oversized message. -/
example (ctor : ConstructorSpec) (message : String)
    (occurs : FunctionBody.RequireMessageOccurs ctor.body message)
    (oversized : requirePayloadFitsWord message = false) :
    validateConstructorSpec (some ctor) =
      .error "Compilation error: constructor contains a require message whose ABI Error(string) payload exceeds the EVM word address space." := by
  simp only [validateConstructorSpec, validateRequirePayloads,
    FunctionBody.requireMessageOccurs_overflow occurs oversized, ↓reduceIte]
  change (Except.error _ : Except String Unit) = .error _
  apply congrArg Except.error
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  decide +kernel


/-- A public helper result retains its actual body frame and receipt schedule. -/
example (spec : CompilationModel) (fn : FunctionSpec) (fuel : Nat)
    (tx : IRTransaction) (initial : Verity.ContractState)
    (oracle : Nat → SourceSemantics.ExternalCallOutcome)
    (context : Option Verity.Core.Model.ExecutionContext) (index : Nat)
    (bindings : List (String × Nat)) (source : SourceSemantics.StmtResult)
    (bound : SourceSemantics.bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (body : SourceSemantics.execStmtListWithHelpers spec (SourceSemantics.effectiveFields spec) fuel
      { world := SourceSemantics.withTransactionContext initial tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle,
        executionContext := context, externalCallIndex := index, errors := spec.errors } fn.body = source) :
    SourceSemantics.interpretFunctionWithHelpers spec fuel fn tx initial oracle context index =
      FunctionBody.stmtResultToSourceResult spec (SourceSemantics.withTransactionContext initial tx) source :=
  public_helper_function_body_result spec fn fuel tx initial oracle context index bindings source bound body

end SolidityImportSmoke.GenericReturndataChecks
