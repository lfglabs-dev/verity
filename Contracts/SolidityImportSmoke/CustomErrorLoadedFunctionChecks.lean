import Compiler.Proofs.IRGeneration.CustomErrorLoadedFunction

namespace SolidityImportSmoke.CustomErrorLoadedFunctionChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics CustomErrorLoadedFunction

example (spec : CompilationModel) (tx : IRTransaction)
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
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) :=
  zero_error_function spec tx world fn compiled definition out bindings oracle helperFuel extra
    params payloadCompiled sourceBody compiledBody supported calldataFits loaded bound unique extent fuel

example (spec : CompilationModel) (selector : Nat)
    (fn : FunctionSpec) (compiled : IRFunction) (definition : ErrorDef) (out : List YulStmt)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      selector fn fork internals = .ok compiled)
    (sourceBody : fn.body = [.revertError definition.name []])
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    compiled.body = genParamLoads fn.bindingParams ++ out :=
  compiled_zero_body spec selector fn compiled definition out fork internals origin sourceBody lookup payloadCompiled

example (fn : IRFunction) (args : List Nat) (state : IRState) :
    (CustomErrorFunctionResult.argumentState fn args state).calldata = state.calldata :=
  argument_calldata fn args state

end SolidityImportSmoke.CustomErrorLoadedFunctionChecks
