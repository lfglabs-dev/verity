import Compiler.Proofs.IRGeneration.CustomErrorCompilationOrigin

namespace Compiler.Proofs.IRGeneration.CustomErrorLoadedFunction
open Compiler.CompilationModel Compiler.Yul SourceSemantics CustomErrorFunctionResult

/-- Prebinding changes variables only; calldata remains the real transaction. -/
theorem argument_calldata (fn : IRFunction) (args : List Nat) (state : IRState) :
    (argumentState fn args state).calldata = state.calldata := by
  unfold argumentState
  induction fn.params.zip args generalizing state with
  | nil => rfl
  | cons entry tail ih =>
      simpa only [List.foldl, IRState.setVar] using ih (state.setVar entry.1.name entry.2)

/-- The actual raw-argument and ABI-binding prefixes preserve physical memory. -/
theorem bound_argument_memory (compiled : IRFunction) (args : List Nat) (state : IRState)
    (bindings : List (String × Nat)) (query : Nat) :
    (ParamLoading.applyBindingsToIRState (argumentState compiled args state) bindings).memory query =
      state.memory query := by
  rw [CustomErrorFunctionEntry.binding_memory, argument_memory]

/-- The zero-argument payload compiler emits exactly one block. -/
theorem zero_payload_length (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    out.length = 1 := by
  rw [PhysicalSignatureExecution.compile_zero_shape .calldata definition params] at compiled
  cases compiled
  rfl

/-- Actual ABI loading from the exact prebound execIRFunction state. -/
theorem loaded_prebound_body (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (compiled : IRFunction) (params : List Param)
    (bindings : List (String × Nat)) (body : List YulStmt) (extra : Nat) (result : IRExecResult)
    (supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (bound : bindSupportedParams params tx.args = some bindings)
    (executed : execIRStmts (body.length + extra + 1)
      (ParamLoading.applyBindingsToIRState
        (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      body = result) :
    execIRStmts ((genParamLoads params).length + body.length + extra + 1)
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))
      (genParamLoads params ++ body) = result := by
  have calldata : (argumentState compiled tx.args
      (FunctionBody.initialIRStateForTx spec tx world)).calldata = tx.args :=
    argument_calldata compiled tx.args _
  have loaded := ParamLoading.exec_genParamLoads_supported_then_extraFuel
    (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))
    params bindings body extra supported (by simpa only [calldata] using calldataFits)
    (by simpa only [calldata] using bound)
  exact loaded.trans executed

/-- Join the actual ABI loader and body execution at the function's structural
fuel. All budget equalities remain obligations; no fuel success is assumed. -/
theorem loaded_body_at_sizeOf (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (compiled : IRFunction) (params : List Param)
    (bindings : List (String × Nat)) (body : List YulStmt) (budget : Nat) (result : IRExecResult)
    (shape : compiled.body = genParamLoads params ++ body)
    (supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (bound : bindSupportedParams params tx.args = some bindings)
    (enough : body.length < budget)
    (fuel : sizeOf compiled.body + 1 = (genParamLoads params).length + budget)
    (executed : execIRStmts budget (ParamLoading.applyBindingsToIRState
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      body = result) :
    execIRStmts (sizeOf compiled.body + 1)
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))
      compiled.body = result := by
  have bodyBudget : body.length + (budget - body.length - 1) + 1 = budget := by omega
  have loaded := loaded_prebound_body spec tx world compiled params bindings body
    (budget - body.length - 1) result supported calldataFits bound
    (by simpa only [bodyBudget] using executed)
  rw [fuel, shape]
  have fullBudget : (genParamLoads params).length + body.length +
      (budget - body.length - 1) + 1 = (genParamLoads params).length + budget := by omega
  simpa only [fullBudget] using loaded

/-- Compose a physically executed error body with the actual ABI loader and
public rollback. The body execution, byte capture and precise fuel are required. -/
theorem loaded_public_error_match (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (bindings : List (String × Nat)) (oracle : Nat → ExternalCallOutcome)
    (helperFuel : Nat) (body : List YulStmt) (budget : Nat) (final : IRState) (data : List UInt8)
    (shape : compiled.body = genParamLoads fn.bindingParams ++ body)
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (enough : body.length < budget)
    (fuel : sizeOf compiled.body + 1 = (genParamLoads fn.bindingParams).length + budget)
    (source : execStmtListWithHelpers spec (effectiveFields spec) helperFuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data)
    (executed : execIRStmts budget (ParamLoading.applyBindingsToIRState
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      body = .revert final)
    (captured : final.revertBytes = some data) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  apply public_error_match spec tx world fn compiled bindings oracle helperFuel final data bound source
  · exact loaded_body_at_sizeOf spec tx world compiled fn.bindingParams bindings body budget
      (.revert final) shape supported calldataFits loaded enough fuel executed
  · exact captured

/-- Concrete zero-argument custom-error function: actual payload generation,
physical execution, prebinding, ABI loader and public rollback. No body-result
oracle is required; exact executor sizeOf fuel and compiler shapes stay visible. -/
theorem zero_error_function (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel extra : Nat)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.revertError definition.name []])
    (compiledBody : compiled.body = genParamLoads fn.bindingParams ++ out)
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (extent : (world.memory freeMemoryPointer).val +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus)
    (fuel : sizeOf compiled.body + 1 = (genParamLoads fn.bindingParams).length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  let state := ParamLoading.applyBindingsToIRState
    (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings
  let runtime : RuntimeState :=
    { world := withTransactionContext world tx, bindings := bindings,
      selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
  have pointer : state.memory freeMemoryPointer = (world.memory freeMemoryPointer).val :=
    CustomErrorLoadedFunction.bound_argument_memory compiled tx.args _ bindings _
  obtain ⟨actual, final, data, payload, executed, captured, source⟩ :=
    PhysicalCustomErrorExecution.compiled_zero_source_bytes .calldata definition params state extra
      (effectiveFields spec) runtime unique (by simpa only [pointer] using extent)
  have same : actual = out := Except.ok.inj (payload.symm.trans payloadCompiled)
  subst actual
  have outLength := zero_payload_length definition out params payloadCompiled
  have sourceExecuted : execStmtListWithHelpers spec (effectiveFields spec) helperFuel runtime
      fn.body = .revertWithData data := by
    simp only [sourceBody, execStmtListWithHelpers, execStmtWithHelpers, source]
  apply public_error_match spec tx world fn compiled bindings oracle helperFuel final data bound sourceExecuted
  · apply loaded_body_at_sizeOf spec tx world compiled fn.bindingParams bindings out
      ((PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7) (.revert final) compiledBody supported calldataFits loaded
    · rw [outLength]; omega
    · simpa only [Nat.add_assoc] using fuel
    · exact executed
  · exact captured

/-- The loader/payload shape is derived from actual function compilation for
this error-ending body, for any fork and internal-function table. -/
theorem compiled_zero_body (spec : CompilationModel) (selector : Nat)
    (fn : FunctionSpec) (compiled : IRFunction) (definition : ErrorDef) (out : List YulStmt)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      selector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.revertError definition.name []])
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    compiled.body = genParamLoads fn.bindingParams ++ out := by
  obtain ⟨returns, actual, _, lowered, shape⟩ := CustomErrorCompilationOrigin.components
    (effectiveFields spec) spec.events spec.errors spec.adtTypes selector fn fork internals compiled origin
  have actualEq : actual = out := by
    have compiledList : compileStmtListWithFork (effectiveFields spec) spec.events spec.errors
        .calldata [] false (fn.bindingParams.map (·.name)) spec.adtTypes fork fn.body internals = .ok out := by
      simp [sourceBody, compileStmtListWithFork, compileStmtWithFork, lookup,
        compileExprListWithInternals, payloadCompiled, bind, Except.bind, pure, Except.pure]
    exact Except.ok.inj (lowered.symm.trans compiledList)
  simpa only [shape, actualEq]

end Compiler.Proofs.IRGeneration.CustomErrorLoadedFunction
