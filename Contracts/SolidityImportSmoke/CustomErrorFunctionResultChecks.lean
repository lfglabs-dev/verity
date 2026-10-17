import Compiler.Proofs.IRGeneration.CustomErrorFunctionResult

namespace SolidityImportSmoke.CustomErrorFunctionResultChecks
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open SourceSemantics IRMemoryCoherence CustomErrorFunctionResult

example (fn : IRFunction) (args : List Nat) (state final : IRState)
    (data : List UInt8)
    (executed : execIRStmts (sizeOf fn.body + 1) (argumentState fn args state) fn.body = .revert final)
    (captured : final.revertBytes = some data) :
    execIRFunction fn args state =
      { success := false, returnValue := none, revertData := some data,
        finalStorage := state.storage,
        finalMappings := Compiler.Proofs.storageAsMappings state.storage, events := state.events } :=
  function_revert fn args state final data executed captured

example (spec : CompilationModel) (tx : IRTransaction)
    (world : Verity.ContractState) (fn : FunctionSpec) (compiled : IRFunction)
    (bindings : List (String × Nat)) (oracle : Nat → ExternalCallOutcome)
    (helperFuel : Nat) (final : IRState) (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (source : execStmtListWithHelpers spec (effectiveFields spec) helperFuel
      { world := withTransactionContext world tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data)
    (executed : execIRStmts (sizeOf compiled.body + 1)
      (argumentState compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))
      compiled.body = .revert final)
    (captured : final.revertBytes = some data) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) :=
  public_error_match spec tx world fn compiled bindings oracle helperFuel final data bound source executed captured

example (fn : IRFunction) (args : List Nat) (state : IRState) :
    (argumentState fn args state).memory freeMemoryPointer = state.memory freeMemoryPointer :=
  argument_memory fn args state freeMemoryPointer

end SolidityImportSmoke.CustomErrorFunctionResultChecks
