import Compiler.Proofs.IRGeneration.CustomErrorFunctionEntry

namespace SolidityImportSmoke.CustomErrorFunctionEntryChecks
open Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics IRMemoryCoherence CustomErrorFunctionEntry

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome)
    (coherent : PhysicalMemory.Coherent world)
    (fits : ∀ definition ∈ spec.errors,
      (world.memory freeMemoryPointer).val +
        32 * (chunkBytes32 (bytesFromString (errorSignature definition))).length ≤
          Verity.Core.Uint256.modulus) :
    CustomErrorDomain spec
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      (ParamLoading.applyBindingsToIRState (FunctionBody.initialIRStateForTx spec tx world) bindings) ∧
    Coherent (ParamLoading.applyBindingsToIRState
      (FunctionBody.initialIRStateForTx spec tx world) bindings) :=
  entry_domain spec tx world bindings oracle coherent fits

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (params : List Param) (bindings : List (String × Nat))
    (body : List YulStmt) (extra : Nat) (result : IRExecResult)
    (supported : ∀ param ∈ params, SupportedExternalScalarParamType param.ty)
    (calldataFits : 4 + tx.args.length * 32 < Compiler.Constants.evmModulus)
    (bound : bindSupportedParams params tx.args = some bindings)
    (executed : execIRStmts (body.length + extra + 1)
      (ParamLoading.applyBindingsToIRState
        (FunctionBody.initialIRStateForTx spec tx world) bindings) body = result) :
    execIRStmts ((genParamLoads params).length + body.length + extra + 1)
      (FunctionBody.initialIRStateForTx spec tx world) (genParamLoads params ++ body) = result :=
  loaded_body spec tx world params bindings body extra result supported calldataFits bound executed

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (bindings : List (String × Nat))
    (oracle : Nat → ExternalCallOutcome) (fuel : Nat) (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithHelpers spec (effectiveFields spec) fuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data) :
    interpretFunctionWithHelpers spec fuel fn tx world oracle =
      { revertedResult spec (withTransactionContext world tx) with revertData := data } :=
  public_source_error spec tx world fn bindings oracle fuel data bound executed

end SolidityImportSmoke.CustomErrorFunctionEntryChecks
