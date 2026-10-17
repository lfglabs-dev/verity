import Compiler.Proofs.IRGeneration.CustomErrorConditionalFunction

namespace SolidityImportSmoke.CustomErrorConditionalFunctionChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics PhysicalSignatureExecution CustomErrorFunctionResult CustomErrorConditionalFunction

example (pre : List YulStmt) (definition : ErrorDef) (out : List YulStmt)
    (cond : YulExpr) (params : definition.params = [])
    (compiled : revertWithCustomError .calldata definition [] [] = .ok out) :
    ∃ extra, sizeOf (pre ++ [.if_ cond out]) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 9 :=
  zero_conditional_extra pre definition out cond params compiled

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork) (internals : List FunctionSpec)
    (cond : Expr) (failCond : YulExpr)
    (origin : compileFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
      tx.functionSelector fn fork internals = .ok compiled)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.requireError cond definition.name []])
    (condition : compileRequireFailCondWithInternals (effectiveFields spec) .calldata
      internals cond = .ok failCond)
    (sourceCond : evalExprWithHelpers spec (effectiveFields spec) helperFuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      cond = some 0)
    (compiledCond : evalIRExpr
      (ParamLoading.applyBindingsToIRState
        (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
      failCond = some 1)
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
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_zero_failure spec tx world fn compiled definition out bindings oracle helperFuel fork internals cond failCond origin lookup params payloadCompiled sourceBody condition sourceCond compiledCond supported calldataFits loaded bound unique extent

end SolidityImportSmoke.CustomErrorConditionalFunctionChecks
