import Compiler.Proofs.IRGeneration.GenericInduction.ResultRelation
import Compiler.Proofs.IRGeneration.CustomErrorExpressionFrame

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel Compiler.Yul

/-- Actual statement compilation and canonical Source execution agree on the
complete zero-argument custom-error payload. Both declaration lookups are
explicit; arbitrary runtimes are not assumed to share the compiler's errors. -/
theorem compiled_revertError_zero_exact_bytes
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (definition : ErrorDef) (extra : Nat)
    (params : definition.params = [])
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition])
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out sourceResult irExec,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.revertError definition.name []) = .ok out ∧
      SourceSemantics.execStmt fields runtime (.revertError definition.name []) = sourceResult ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError definition.name []))
        sourceResult irExec := by
  obtain ⟨out, final, data, compiled, executed, bytes, sourceBytes⟩ :=
    PhysicalCustomErrorExecution.compiled_zero_source_bytes .calldata definition params state extra
      fields runtime runtimeLookup extent
  refine ⟨out, .revertWithData data, .revert final, ?_, ?_, executed, ?_⟩
  · simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      compilerLookup, compileExprListWithInternals, pure, Except.pure,
      Bind.bind, Except.bind] using compiled
  · simpa only [SourceSemantics.execStmt] using sourceBytes
  · exact bytes

open PhysicalCustomErrorScalarExecution CustomErrorExpressionFrame

theorem compiled_revertError_scalar_exact_bytes (definition : ErrorDef) (fields : List Field)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (scope : List String) (errors : List ErrorDef)
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals fields .calldata [] [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty]) (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (state : IRState) (value extra : Nat)
    (runtime : SourceSemantics.RuntimeState) (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr) :
    ∃ out sourceResult irExec,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.revertError definition.name [srcExpr]) = .ok out ∧
      SourceSemantics.execStmt fields runtime (.revertError definition.name [srcExpr]) = sourceResult ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8) state out = irExec ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.revertError definition.name [srcExpr]))
        sourceResult irExec := by
  obtain ⟨out, final, data, compiled, executed, bytes, sourceBytes⟩ :=
    compiled_recursive_source_bytes .calldata definition ty srcExpr argExpr encoded params scalar encoding
      state value extra fields runtime typeName evaluated resolved canonical supported extent
      argument supportedExpr
  refine ⟨out, .revertWithData data, .revert final, ?_, ?_, executed, ?_⟩
  · simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      compilerLookup, compiledArgs, pure, Except.pure, Bind.bind, Except.bind] using compiled
  · simpa only [SourceSemantics.execStmt] using sourceBytes
  · exact bytes

/-- A failing require executes the actual error block with two additional
interpreter stages; the payload is the one actually captured by that block. -/
theorem requireError_failure_exact_bytes (fields : List Field) (scope : List String)
    (runtime : SourceSemantics.RuntimeState) (state final : IRState)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr)
    (out : List YulStmt) (data : List UInt8) (fuel : Nat)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (sourceError : SourceSemantics.execStmt fields runtime (.revertError name args) =
      .revertWithData data)
    (executed : execIRStmts fuel state out = .revert final)
    (payload : final.revertBytes = some data) :
    SourceSemantics.execStmt fields runtime (.requireError cond name args) = .revertWithData data ∧
    execIRStmts (fuel + 2) state [.if_ failCond out] = .revert final ∧
    stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond name args))
      (.revertWithData data) (.revert final) := by
  refine ⟨?_, ?_, payload⟩
  · simpa [SourceSemantics.execStmt, sourceCond] using sourceError
  · have step : execIRStmt (fuel + 1) state (.if_ failCond out) = .revert final := by
      simp only [execIRStmt, compiledCond]
      exact executed
    rw [show fuel + 2 = (fuel + 1) + 1 by omega]
    simp only [execIRStmts, step]

theorem compile_requireError_from_revertError
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (cond : Expr) (name : String) (args : List Expr) (failCond : YulExpr) (out : List YulStmt)
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (error : CompilationModel.compileStmt fields [] errors .calldata [] false scope []
      (.revertError name args) = .ok out) :
    CompilationModel.compileStmt fields [] errors .calldata [] false scope []
      (.requireError cond name args) = .ok [.if_ failCond out] := by
  unfold CompilationModel.compileStmt CompilationModel.compileStmtWithFork at error ⊢
  simp only [condition, Bind.bind, Except.bind, pure, Except.pure] at error ⊢
  cases lookup : errors.find? (·.name == name) with
  | none => simp [lookup] at error
  | some definition =>
      cases compiled : compileExprListWithInternals fields .calldata [] args with
      | error message => simp [lookup, compiled] at error
      | ok argExprs =>
          cases payload : revertWithCustomError .calldata definition args argExprs with
          | error message => simp [lookup, compiled, payload] at error
          | ok result =>
              simp [lookup, compiled, payload] at error ⊢
              exact error

theorem compiled_requireError_zero_failure_exact_bytes
    (fields : List Field) (scope : List String) (errors : List ErrorDef)
    (runtime : SourceSemantics.RuntimeState) (state : IRState)
    (definition : ErrorDef) (cond : Expr) (failCond : YulExpr) (extra : Nat)
    (params : definition.params = [])
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (runtimeLookup : runtime.errors.filter (·.name == definition.name) = [definition])
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    ∃ out data final,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.requireError cond definition.name []) = .ok [.if_ failCond out] ∧
      SourceSemantics.execStmt fields runtime (.requireError cond definition.name []) =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9)
        state [.if_ failCond out] = .revert final ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope (.requireError cond definition.name []))
        (.revertWithData data) (.revert final) := by
  obtain ⟨out, final, data, compiled, executed, payload, sourceBytes⟩ :=
    PhysicalCustomErrorExecution.compiled_zero_source_bytes .calldata definition params state extra
      fields runtime runtimeLookup extent
  have revertCompile : CompilationModel.compileStmt fields [] errors .calldata [] false scope []
      (.revertError definition.name []) = .ok out := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      compilerLookup, compileExprListWithInternals, pure, Except.pure, Bind.bind, Except.bind] using compiled
  have sourceError : SourceSemantics.execStmt fields runtime (.revertError definition.name []) =
      .revertWithData data := by simpa only [SourceSemantics.execStmt] using sourceBytes
  have failure := requireError_failure_exact_bytes fields scope runtime state final cond definition.name []
    failCond out data _ sourceCond compiledCond sourceError executed payload
  refine ⟨out, data, final, compile_requireError_from_revertError fields scope errors cond
    definition.name [] failCond out condition revertCompile, failure.1, ?_, failure.2.2⟩
  simpa only [Nat.add_assoc] using failure.2.1

/-- Actual scalar custom-error compilation through a failing require. Both
condition evaluations and the initial argument evaluation are explicit; the
scratch frame and canonical encoder derive the bytes after the real prefix. -/
theorem compiled_requireError_scalar_failure_exact_bytes
    (definition : ErrorDef) (fields : List Field) (scope : List String)
    (errors : List ErrorDef) (ty : ParamType) (srcExpr cond : Expr)
    (argExpr encoded failCond : YulExpr)
    (compilerLookup : errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals fields .calldata [] [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (condition : compileRequireFailCondWithInternals fields .calldata [] cond = .ok failCond)
    (runtime : SourceSemantics.RuntimeState) (state : IRState) (value extra : Nat)
    (typeName : String)
    (evaluated : SourceSemantics.evalExprList fields runtime [srcExpr] = some [value])
    (resolved : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (supported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (supportedExpr : ScratchExpr argExpr)
    (sourceCond : SourceSemantics.evalExpr fields runtime cond = some 0)
    (compiledCond : evalIRExpr state failCond = some 1) :
    ∃ out data final,
      CompilationModel.compileStmt fields [] errors .calldata [] false scope []
        (.requireError cond definition.name [srcExpr]) = .ok [.if_ failCond out] ∧
      SourceSemantics.execStmt fields runtime (.requireError cond definition.name [srcExpr]) =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 10)
        state [.if_ failCond out] = .revert final ∧
      stmtStepMatchesIRExec fields (stmtNextScope scope
        (.requireError cond definition.name [srcExpr])) (.revertWithData data) (.revert final) := by
  obtain ⟨out, final, data, compiled, executed, payload, sourceBytes⟩ :=
    compiled_recursive_source_bytes .calldata definition ty srcExpr argExpr encoded params scalar encoding
      state value extra fields runtime typeName evaluated resolved canonical supported extent
      argument supportedExpr
  have revertCompile : CompilationModel.compileStmt fields [] errors .calldata [] false scope []
      (.revertError definition.name [srcExpr]) = .ok out := by
    simpa [CompilationModel.compileStmt, CompilationModel.compileStmtWithFork,
      compilerLookup, compiledArgs, pure, Except.pure, Bind.bind, Except.bind] using compiled
  have sourceError : SourceSemantics.execStmt fields runtime
      (.revertError definition.name [srcExpr]) = .revertWithData data := by
    simpa only [SourceSemantics.execStmt] using sourceBytes
  have failure := requireError_failure_exact_bytes fields scope runtime state final cond definition.name
    [srcExpr] failCond out data _ sourceCond compiledCond sourceError executed payload
  refine ⟨out, data, final, compile_requireError_from_revertError fields scope errors cond
    definition.name [srcExpr] failCond out condition revertCompile, failure.1, ?_, failure.2.2⟩
  simpa only [Nat.add_assoc] using failure.2.1

end Compiler.Proofs.IRGeneration
