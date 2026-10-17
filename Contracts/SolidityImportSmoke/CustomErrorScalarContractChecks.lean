import Compiler.Proofs.IRGeneration.CustomErrorScalarContract

namespace SolidityImportSmoke.CustomErrorScalarContractChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics CustomErrorFunctionResult CustomErrorScalarContract

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (contract : IRContract) (selectors : List Nat)
    (definition : ErrorDef) (ty : ParamType) (srcExpr : Expr) (argExpr encoded : YulExpr)
    (out : List YulStmt) (bindings : List (String × Nat)) (value : Nat) (typeName : String)
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (unlocked : fn.nonReentrantLock = none)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentCount : fn.params.length ≤ tx.args.length)
    (sourceBody : fn.body = [.revertError definition.name [srcExpr]])
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (compiledArgs : compileExprListWithInternals (effectiveFields spec) .calldata (spec.functions.filter (·.isInternal)) [srcExpr] = .ok [argExpr])
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
    (argument : ∀ compiled,
      compileGuardedFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
        (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork = .ok compiled →
      evalIRExpr (ParamLoading.applyBindingsToIRState
        (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) bindings)
        argExpr = some value)
    (expression : CustomErrorExpressionFrame.ScratchExpr argExpr) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) :=
  compiled_scalar_error_contract spec tx world fn contract selectors definition ty srcExpr argExpr encoded
    out bindings value typeName oracle helperFuel fork origin selected unlocked admitted argumentCount
    sourceBody lookup compiledArgs params scalar encoding payloadCompiled supported calldataFits loaded bound
    unique extent evaluated canonical typeSupported argument expression

end SolidityImportSmoke.CustomErrorScalarContractChecks
