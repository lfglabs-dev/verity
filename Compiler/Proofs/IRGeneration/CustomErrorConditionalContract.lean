import Compiler.Proofs.IRGeneration.CustomErrorConditionalFunction

namespace Compiler.Proofs.IRGeneration.CustomErrorConditionalContract
open Compiler.CompilationModel Compiler.Yul SourceSemantics PhysicalSignatureExecution
open CustomErrorFunctionResult CustomErrorConditionalFunction

/-- Full compiler/dispatcher composition for a selected unguarded failing
conditional zero-error entry. Other contract entries remain unrestricted. -/
theorem compiled_zero_failure_contract (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (contract : IRContract) (selectors : List Nat)
    (definition : ErrorDef) (out : List YulStmt) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (helperFuel : Nat)
    (fork : Verity.Core.Intrinsics.HardFork)
    (cond : Expr) (failCond : YulExpr)
    (origin : Compiler.CompilationModel.compile spec selectors fork = .ok contract)
    (selected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (unlocked : fn.nonReentrantLock = none)
    (admitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentCount : fn.params.length ≤ tx.args.length)
    (lookup : spec.errors.find? (·.name == definition.name) = some definition)
    (params : definition.params = [])
    (payloadCompiled : revertWithCustomError .calldata definition [] [] = .ok out)
    (sourceBody : fn.body = [.requireError cond definition.name []])
    (condition : compileRequireFailCondWithInternals (effectiveFields spec) .calldata
      (spec.functions.filter (·.isInternal)) cond = .ok failCond)
    (sourceCond : evalExprWithHelpers spec (effectiveFields spec) helperFuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      cond = some 0)
    (compiledCond : ∀ compiled,
      compileGuardedFunctionSpec (effectiveFields spec) spec.events spec.errors spec.adtTypes
        (spec.functions.filter (·.isInternal)) tx.functionSelector fn fork = .ok compiled →
      evalIRExpr (ParamLoading.applyBindingsToIRState
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
      (interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  apply CustomErrorContractCompilation.compiled_unguarded_contract_match spec selectors fork contract tx
    world fn helperFuel oracle origin selected unlocked admitted argumentCount
  intro compiled guarded functionOrigin
  exact compiled_zero_failure spec tx world fn compiled definition out bindings oracle helperFuel
    fork (spec.functions.filter (·.isInternal)) cond failCond functionOrigin lookup params
    payloadCompiled sourceBody condition sourceCond (compiledCond compiled guarded) supported
    calldataFits loaded bound unique extent

end Compiler.Proofs.IRGeneration.CustomErrorConditionalContract
