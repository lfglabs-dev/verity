import Compiler.Proofs.IRGeneration.CustomErrorFunctionFuel

namespace SolidityImportSmoke.CustomErrorFunctionFuelChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics CustomErrorFunctionFuel

example (spec : CompilationModel) (tx : IRTransaction)
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
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_zero_error_contract spec tx world fn contract selectors definition out bindings oracle helperFuel
    fork origin selected unlocked admitted argumentCount lookup params payloadCompiled sourceBody
    supported calldataFits loaded bound unique extent

/-- Structural fuel covers any generated signature length and loader prefix. -/
example (pre : List YulStmt) (definition : ErrorDef) (out : List YulStmt)
    (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    ∃ extra, sizeOf (pre ++ out) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 7 :=
  zero_payload_extra pre definition out params compiled

end SolidityImportSmoke.CustomErrorFunctionFuelChecks
