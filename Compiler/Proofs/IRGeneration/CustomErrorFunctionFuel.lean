import Compiler.Proofs.IRGeneration.CustomErrorLoadedFunction
import Compiler.Proofs.IRGeneration.CustomErrorContractCompilation

namespace Compiler.Proofs.IRGeneration.CustomErrorFunctionFuel
open Compiler.CompilationModel Compiler.Yul PhysicalSignatureExecution SourceSemantics

private theorem length_le_size (body : List YulStmt) : body.length ≤ sizeOf body := by
  induction body with
  | nil => simp
  | cons stmt rest ih => simp; omega

private theorem block_budget (pre body : List YulStmt) :
    pre.length + body.length + 3 ≤ sizeOf (pre ++ [.block body]) := by
  induction pre with
  | nil =>
    have bounded := length_le_size body
    simp
    omega
  | cons stmt rest ih =>
    simp at *
    omega

/-- The real block payload provides enough structural executor fuel, even
when the generated signature requires arbitrarily many chunk stores. -/
theorem zero_payload_fuel (pre : List YulStmt) (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    pre.length + (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition))).length + 7 ≤ sizeOf (pre ++ out) + 1 := by
  rw [compile_zero_shape .calldata definition params] at compiled
  cases compiled
  have bounded := block_budget pre
    (PhysicalCustomErrorExecution.signaturePrefix (bytesFromString (errorSignature definition)) ++ zeroSuffix)
  have lengths : (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition)) ++ zeroSuffix).length =
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 4 := by
    simp only [List.length_append, zeroSuffix, List.length_cons, List.length_nil]
  rw [lengths] at bounded
  have enough : pre.length + (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition))).length + 7 ≤
      sizeOf (pre ++ [.block (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition)) ++ zeroSuffix)]) + 1 := by omega
  simpa only [PhysicalCustomErrorExecution.signaturePrefix, List.cons_append,
    List.append_assoc] using enough

/-- The sufficient physical-payload extra fuel is derived, never assumed. -/
theorem zero_payload_extra (pre : List YulStmt) (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    ∃ extra, sizeOf (pre ++ out) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7 := by
  have enough := zero_payload_fuel pre definition out params compiled
  obtain ⟨extra, equation⟩ := Nat.exists_eq_add_of_le enough
  exact ⟨extra, by omega⟩

/-- Actual compilation determines the body shape and structural fuel; only
real ABI/declaration/memory admission premises remain for this error path. -/
theorem compiled_zero_error_function (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (SourceSemantics.effectiveFields spec) spec.events spec.errors
      spec.adtTypes tx.functionSelector fn fork internals = .ok compiled)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.revertError definition.name []])
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (extent : (world.memory freeMemoryPointer).val +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  have shape := CustomErrorLoadedFunction.compiled_zero_body spec tx.functionSelector fn compiled
    definition out fork internals origin sourceBody lookup payloadCompiled
  obtain ⟨extra, fuel⟩ := zero_payload_extra (genParamLoads fn.bindingParams) definition out params payloadCompiled
  apply CustomErrorLoadedFunction.zero_error_function spec tx world fn compiled definition out
    bindings oracle helperFuel extra params payloadCompiled sourceBody shape supported calldataFits
    loaded bound unique extent
  simpa only [shape] using fuel

/-- Complete compiler/dispatcher result for this concrete unguarded error path.
Other entries in the compiled contract may carry guards or internal helpers. -/
theorem compiled_zero_error_contract (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (contract : IRContract) (selectors : List Nat)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (unlocked : fn.nonReentrantLock = none)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentCount : fn.params.length ≤ tx.args.length)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.revertError definition.name []])
    (supported : ∀ param ∈ fn.bindingParams, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (loaded : bindSupportedParams fn.bindingParams tx.args = some bindings)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (unique : spec.errors.filter (·.name == definition.name) = [definition])
    (extent : (world.memory freeMemoryPointer).val +
      32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
        Verity.Core.Uint256.modulus) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  apply CustomErrorContractCompilation.compiled_contract_match spec selectors fork contract tx
    world fn helperFuel oracle origin selected admitted argumentCount
  intro compiled guarded
  have functionOrigin := CustomErrorCompilationOrigin.unguarded_origin
    (effectiveFields spec) spec.events spec.errors spec.adtTypes (spec.functions.filter (·.isInternal))
    tx.functionSelector fn fork compiled unlocked guarded
  exact compiled_zero_error_function spec tx world fn compiled definition out bindings oracle
    helperFuel fork (spec.functions.filter (·.isInternal)) functionOrigin lookup params payloadCompiled
    sourceBody supported calldataFits loaded bound unique extent

/-- Structural executor budget for the actual scalar error payload block. -/
theorem scalar_payload_extra (pre : List YulStmt) (definition : ErrorDef)
    (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr) (out : List YulStmt)
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (compiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out) :
    ∃ extra, sizeOf (pre ++ out) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8 := by
  rw [PhysicalCustomErrorScalarExecution.compile_scalar_shape .calldata definition ty srcExpr
    argExpr encoded params scalar encoding] at compiled
  cases compiled
  have bounded := block_budget pre
    (PhysicalCustomErrorExecution.signaturePrefix (bytesFromString (errorSignature definition)) ++
      PhysicalCustomErrorScalarExecution.scalarSuffix encoded)
  have lengths : (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition)) ++
      PhysicalCustomErrorScalarExecution.scalarSuffix encoded).length =
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + 5 := by
    simp only [List.length_append, PhysicalCustomErrorScalarExecution.scalarSuffix,
      List.length_cons, List.length_nil]
  rw [lengths] at bounded
  have enough : pre.length + (PhysicalCustomErrorExecution.signaturePrefix
      (bytesFromString (errorSignature definition))).length + 8 ≤
      sizeOf (pre ++ [.block (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition)) ++
          PhysicalCustomErrorScalarExecution.scalarSuffix encoded)]) + 1 := by omega
  obtain ⟨extra, equation⟩ := Nat.exists_eq_add_of_le enough
  exact ⟨extra, by omega⟩

end Compiler.Proofs.IRGeneration.CustomErrorFunctionFuel
