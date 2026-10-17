import Compiler.Proofs.IRGeneration.CustomErrorScalarFunction

namespace SolidityImportSmoke.CustomErrorScalarFunctionChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics CustomErrorFunctionResult CustomErrorScalarFunction

example (spec : CompilationModel) (tx : IRTransaction)
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
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_scalar_error_function spec tx world fn compiled definition ty srcExpr argExpr encoded out
    bindings value typeName oracle helperFuel fork internals origin sourceBody lookup compiledArgs params
    scalar encoding payloadCompiled supported calldataFits loaded bound unique extent evaluated canonical
    typeSupported argument expression

/-- Actual scalar-payload shape provides sufficient structural fuel for any
signature chunk count and any generated parameter-loader prefix. -/
example (pre : List YulStmt) (definition : ErrorDef) (ty : ParamType)
    (srcExpr : Expr) (argExpr encoded : YulExpr) (out : List YulStmt)
    (params : definition.params = [ty])
    (scalar : PhysicalCustomErrorScalarExecution.staticScalar ty = true)
    (encoding : encodeStaticCustomErrorArg definition.name ty argExpr = .ok encoded)
    (compiled : revertWithCustomError .calldata definition [srcExpr] [argExpr] = .ok out) :
    ∃ extra, sizeOf (pre ++ out) + 1 = pre.length +
      (PhysicalCustomErrorExecution.signaturePrefix
        (bytesFromString (errorSignature definition))).length + extra + 8 :=
  CustomErrorFunctionFuel.scalar_payload_extra pre definition ty srcExpr argExpr encoded out
    params scalar encoding compiled

end SolidityImportSmoke.CustomErrorScalarFunctionChecks
