import Compiler.Proofs.IRGeneration.CustomErrorFunctionFuel

namespace Compiler.Proofs.IRGeneration.CustomErrorScalarFunction
open Compiler.CompilationModel Compiler.Yul SourceSemantics CustomErrorFunctionResult

/-- The actual scalar-error function compiler fixes the ABI-prefixed body. -/
theorem compiled_scalar_body (spec : CompilationModel) (selector : Nat)
    (fn : FunctionSpec) (compiled : IRFunction) (definition : ErrorDef)
    (srcExpr : Expr) (argExpr : YulExpr) (out : List YulStmt)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      selector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.revertError definition.name [srcExpr]])
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals (effectiveFields spec) .calldata internals
      [srcExpr] = .ok [argExpr])
    (payloadCompiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out) :
    compiled.body = genParamLoads fn.bindingParams ++ out := by
  obtain ⟨returns, actualBody, _, lowered, compilerShape⟩ := CustomErrorCompilationOrigin.components
    (effectiveFields spec) spec.events spec.errors spec.adtTypes selector fn fork internals compiled origin
  have actualEq : actualBody = out := by
    have bodyCompiled : compileStmtListWithFork (effectiveFields spec) spec.events spec.errors
        .calldata [] false (fn.bindingParams.map (·.name)) spec.adtTypes fork fn.body internals = .ok out := by
      simp [sourceBody, compileStmtListWithFork, compileStmtWithFork, lookup,
        compiledArgs, payloadCompiled, bind, Except.bind, pure, Except.pure]
    exact Except.ok.inj (lowered.symm.trans bodyCompiled)
  simpa only [compilerShape, actualEq]

/-- The scalar payload compiler emits a singleton physical block. -/
theorem scalar_payload_length (definition : ErrorDef) (ty : ParamType)
    (srcExpr : Expr) (argExpr encoded : YulExpr) (out : List YulStmt)
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (compiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out) :
    out.length = 1 := by
  rw [PhysicalCustomErrorScalarExecution.compile_scalar_shape .calldata definition ty srcExpr argExpr
    encoded params scalar encoding] at compiled
  cases compiled
  rfl

/-- A scalar payload has one physical block and the same typed Source error.
This lemma is independent of function compilation and ABI prebinding. -/
theorem scalar_body_execution (spec : CompilationModel) (fields : List Field)
    (runtime : RuntimeState) (state : IRState) (helperFuel extra : Nat)
    (definition : ErrorDef) (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (out : List YulStmt) (value : Nat) (typeName : String)
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (payloadCompiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out)
    (evaluated : evalExprList fields runtime [srcExpr] = some [value])
    (unique : runtime.errors.filter (·.name == definition.name) = [definition])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (typeSupported : Denote.errorScalarType ty = some typeName)
    (extent : state.memory freeMemoryPointer +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤ Verity.Core.Uint256.modulus)
    (argument : evalIRExpr state argExpr = some value)
    (expression : CustomErrorExpressionFrame.ScratchExpr argExpr) :
    ∃ final data, out.length = 1 ∧
      execStmtListWithHelpers spec fields helperFuel runtime [.revertError definition.name [srcExpr]] =
        .revertWithData data ∧
      execIRStmts ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8) state out = .revert final ∧
      final.revertBytes = some data := by
  obtain ⟨actual, final, data, payload, executed, captured, source⟩ :=
    CustomErrorExpressionFrame.compiled_recursive_source_bytes .calldata definition ty srcExpr argExpr
      encoded params scalar encoding state value extra fields runtime typeName
      evaluated unique canonical typeSupported extent argument expression
  have same : actual = out := Except.ok.inj (payload.symm.trans payloadCompiled)
  subst actual
  refine ⟨final, data, scalar_payload_length definition ty srcExpr argExpr encoded out
    params scalar encoding payloadCompiled, ?_, executed, captured⟩
  simp only [execStmtListWithHelpers, execStmtWithHelpers, source]

/-- Scalar error function with actual compiler origin and physical payload,
prebinding/ABI execution and derived sizeOf fuel. Initial Source and IR argument
observations remain explicit; scratch-dependent expressions are not admitted. -/
theorem compiled_scalar_error_function (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (definition : ErrorDef) (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (out : List YulStmt) (bindings : List (String × Nat)) (value : Nat) (typeName : String)
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      tx.functionSelector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.revertError definition.name [srcExpr]])
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals (effectiveFields spec) .calldata internals [srcExpr] = .ok [argExpr])
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (payloadCompiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out)
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (extent : (world.memory freeMemoryPointer).val +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (evaluated : evalExprList (effectiveFields spec)
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      [srcExpr] = some [value])
    (canonical : Denote.errorScalarValueValid ty value = true)
    (typeSupported : Denote.errorScalarType ty = some typeName)
    (argument : evalIRExpr (ParamLoading.applyBindingsToIRState
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      argExpr = some value)
    (expression : CustomErrorExpressionFrame.ScratchExpr argExpr) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  have shape := compiled_scalar_body spec tx.functionSelector fn compiled definition srcExpr argExpr
    out fork internals origin sourceBody lookup compiledArgs payloadCompiled
  obtain ⟨extra, fuel⟩ := CustomErrorFunctionFuel.scalar_payload_extra
    (genParamLoads fn.bindingParams) definition ty srcExpr argExpr encoded out params scalar encoding payloadCompiled
  obtain ⟨final, data, outLength, source, executed, captured⟩ := scalar_body_execution spec
    (effectiveFields spec) _ _ helperFuel extra definition ty srcExpr argExpr encoded out value typeName
    params scalar encoding payloadCompiled evaluated unique canonical typeSupported
    (by simpa only [CustomErrorLoadedFunction.bound_argument_memory, FunctionBody.initialIRStateForTx] using extent) argument expression
  exact CustomErrorLoadedFunction.loaded_public_error_match spec tx world fn compiled bindings oracle
    helperFuel out _ final data shape supported calldataFits loaded bound (by rw [outLength]; omega)
    (by simpa only [shape, Nat.add_assoc] using fuel)
    (by simpa only [sourceBody] using source) executed captured

end Compiler.Proofs.IRGeneration.CustomErrorScalarFunction
