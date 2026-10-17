import Compiler.Proofs.IRGeneration.CustomErrorFunctionEntry
import Compiler.Proofs.IRGeneration.FunctionBody.Stmt

namespace Compiler.Proofs.IRGeneration.CustomErrorFunctionResult
open Compiler.CompilationModel Compiler.Yul SourceSemantics IRMemoryCoherence

/-- Exactly the argument prebinding performed by execIRFunction. -/
def argumentState (fn : IRFunction) (args : List Nat) (state : IRState) : IRState :=
  (fn.params.zip args).foldl (fun current entry => current.setVar entry.1.name entry.2) state

theorem argument_memory (fn : IRFunction) (args : List Nat) (state : IRState) (query : Nat) :
    (argumentState fn args state).memory query = state.memory query := by
  unfold argumentState
  induction fn.params.zip args generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      simpa only [List.foldl, IRState.setVar] using ih (state.setVar entry.1.name entry.2)

theorem argument_coherent (fn : IRFunction) (args : List Nat) (state : IRState)
    (initial : Coherent state) : Coherent (argumentState fn args state) := by
  unfold argumentState
  induction fn.params.zip args generalizing state with
  | nil => exact initial
  | cons entry rest ih =>
      simp only [List.foldl]
      apply ih
      simpa only [Coherent, IRState.setVar] using initial

/-- Actual function rollback and actual captured bytes, at the executor's
sizeOf fuel and exact parameter prebinding. Exhaustion is not payload evidence. -/
theorem function_revert (fn : IRFunction) (args : List Nat) (state final : IRState)
    (data : List UInt8)
    (executed : execIRStmts (sizeOf fn.body + 1) (argumentState fn args state) fn.body = .revert final)
    (captured : final.revertBytes = some data) :
    execIRFunction fn args state =
      { success := false, returnValue := none, revertData := some data,
        finalStorage := state.storage,
        finalMappings := Compiler.Proofs.storageAsMappings state.storage, events := state.events } := by
  change (match execIRStmts (sizeOf fn.body + 1) (argumentState fn args state) fn.body with
    | .continue next => _
    | .return value next => _
    | .stop next => _
    | .exceptional next => _
    | .interpretationError message => _
    | .revert next => _) = _
  simp only [executed, captured]

/-- Join the real public Source function and real IR function observations,
including rollback, every storage observation, events and exact error bytes. -/
theorem public_error_match (spec : CompilationModel) (tx : IRTransaction)
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
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world)) := by
  rw [CustomErrorFunctionEntry.public_source_error spec tx world fn bindings oracle helperFuel data bound source,
    function_revert compiled tx.args _ final data executed captured]
  simp only [FunctionBody.sourceResultMatchesIRResult, revertedResult,
    FunctionBody.initialIRStateForTx]
  simp only [encodeStorage_withTransactionContext]
  simp [withTransactionContext]

/-- Actual dispatcher linkage, with selection and admission obligations explicit. -/
theorem selected_contract_match (spec : CompilationModel) (selectors : List Nat)
    (contract : IRContract) (tx : IRTransaction) (world : Verity.ContractState)
    (fn : FunctionSpec) (compiled : IRFunction) (helperFuel : Nat)
    (oracle : Nat → ExternalCallOutcome)
    (sourceSelected : findFunctionBySelector spec selectors tx.functionSelector = some fn)
    (irSelected : contract.functions.find? (·.selector == tx.functionSelector) = some compiled)
    (sourceAdmitted : (!fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (irAdmitted : (!compiled.payable && tx.msgValue % Compiler.Constants.evmModulus != 0) = false)
    (argumentsAdmitted : compiled.params.length ≤ tx.args.length)
    (body : FunctionBody.sourceResultMatchesIRResult
      (interpretFunctionWithHelpers spec helperFuel fn tx world oracle)
      (execIRFunction compiled tx.args (FunctionBody.initialIRStateForTx spec tx world))) :
    FunctionBody.sourceResultMatchesIRResult
      (interpretContractWithHelpers spec selectors helperFuel tx world oracle)
      (interpretIR contract tx (FunctionBody.initialIRStateForTx spec tx world)) := by
  simpa only [interpretContractWithHelpers, sourceSelected, sourceAdmitted,
    Bool.false_eq_true, ↓reduceIte, dif_pos, interpretIR, FunctionBody.initialIRStateForTx,
    irSelected, irAdmitted, argumentsAdmitted] using body

end Compiler.Proofs.IRGeneration.CustomErrorFunctionResult
