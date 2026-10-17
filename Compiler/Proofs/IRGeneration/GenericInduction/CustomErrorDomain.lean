import Compiler.Proofs.IRGeneration.GenericInduction.CustomErrorBytes
import Compiler.Proofs.IRGeneration.SourceErrorDeclarations

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel Compiler.Yul

/-- The actual function entry supplies the compiler's declarations. Extents
must be proved at the error point; they are not assumed for arbitrary states. -/
structure CustomErrorDomain (spec : CompilationModel)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) : Prop where
  declarations : runtime.errors = spec.errors
  extents : ∀ definition ∈ spec.errors,
    state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus

/-- Exact terminal-error step interface with a visible legal execution domain.
It observes actual Source and IR bytes; the former universal arbitrary-runtime,
arbitrary-fuel coarse revertedness interface cannot supply this certificate. -/
structure CompiledErrorStepWithin
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (stmt : Stmt) (out : List YulStmt) (minimumExtraFuel : Nat) : Prop where
  compileOk : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
    stmt = .ok out
  preserves : ∀ runtime state helperFuel extraFuel,
    CustomErrorDomain spec runtime state → minimumExtraFuel ≤ extraFuel →
    ∃ sourceResult irExec,
      SourceSemantics.execStmtWithHelpers spec fields helperFuel runtime stmt = sourceResult ∧
      execIRStmts (out.length + extraFuel + 1) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope stmt) sourceResult irExec

theorem compiledErrorStep_zero_within
    (spec : CompilationModel) (fields : List Field) (scope : List String)
    (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compilerLookup : spec.errors.find? (·.name == definition.name) = some definition)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (compiled : CompilationModel.compileStmt fields spec.events spec.errors .calldata [] false scope []
      (.revertError definition.name []) = .ok out) :
    CompiledErrorStepWithin spec fields scope (.revertError definition.name []) out
      ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 5) := by
  refine ⟨compiled, ?_⟩
  intro runtime state helperFuel extraFuel domain enough
  have runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition] := by
    rw [domain.declarations]
    exact unique
  have member : definition ∈ spec.errors := List.mem_of_mem_filter
    (by rw [unique]; exact List.mem_singleton_self _)
  have extent := domain.extents definition member
  obtain ⟨extra, fuel⟩ := Nat.exists_eq_add_of_le enough
  obtain ⟨actual, final, data, payloadCompiled, executed, bytes, sourceBytes⟩ :=
    PhysicalCustomErrorExecution.compiled_zero_source_bytes .calldata definition params state extra
      fields runtime runtimeLookup extent
  have same : out = actual := by
    have actualCompiled : CompilationModel.compileStmt fields spec.events spec.errors
        .calldata [] false scope [] (.revertError definition.name []) = .ok actual := by
      simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
        compilerLookup, compileExprListWithInternals, pure, Except.pure, Bind.bind, Except.bind]
        using payloadCompiled
    rw [compiled] at actualCompiled
    exact Except.ok.inj actualCompiled
  subst out
  have length : actual.length = 1 := by
    rw [PhysicalSignatureExecution.compile_zero_shape .calldata definition params] at payloadCompiled
    cases payloadCompiled
    rfl
  refine ⟨.revertWithData data, .revert final, ?_, ?_, bytes⟩
  · simpa only [SourceSemantics.execStmtWithHelpers] using sourceBytes
  · rw [fuel, length]
    have fuelEq : 1 + ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 5 + extra) + 1 =
        (PhysicalCustomErrorExecution.signaturePrefix
          (bytesFromString (errorSignature definition))).length + extra + 7 := by omega
    simpa only [fuelEq] using executed

/-- Continue the domain through the real Source body. Physical extents require
their own IR preservation proof; declaration alignment is derived here. -/
theorem CustomErrorDomain.after_helper_continuation
    (spec : CompilationModel) (fields : List Field) (fuel : Nat)
    (runtime next : SourceSemantics.RuntimeState) (state nextIR : IRState) (body : List Stmt)
    (domain : CustomErrorDomain spec runtime state)
    (executed : SourceSemantics.execStmtListWithHelpers spec fields fuel runtime body = .continue next)
    (physical : ∀ definition ∈ spec.errors,
      nextIR.memory freeMemoryPointer +
        32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
          Verity.Core.Uint256.modulus) :
    CustomErrorDomain spec next nextIR :=
  ⟨SourceErrorDeclarations.helper_continuation_declarations spec fields fuel runtime next body
    domain.declarations executed, physical⟩

end Compiler.Proofs.IRGeneration
