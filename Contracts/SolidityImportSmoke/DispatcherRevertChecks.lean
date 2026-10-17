import Compiler.Proofs.IRGeneration.IRInterpreter

namespace SolidityImportSmoke.DispatcherRevertChecks
open Compiler Compiler.Proofs.IRGeneration

/-- Dispatcher guards emit REVERT(0,0), retaining the caller's state. -/
def exactEmptyRevert (result : IRResult) (initial : IRState) : Prop :=
  result.success = false ∧ result.returnValue = none ∧
  result.interpretationError = none ∧ result.exceptionalContext = none ∧
  result.revertData = some [] ∧ result.finalStorage = initial.storage ∧
  result.finalMappings = Compiler.Proofs.storageAsMappings initial.storage ∧
  result.events = initial.events

theorem unknown (contract : IRContract) (tx : IRTransaction) (initial : IRState)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = none) :
    exactEmptyRevert (interpretIR contract tx initial) initial := by
  simp [interpretIR, exactEmptyRevert, selected]

theorem nonpayable (contract : IRContract) (tx : IRTransaction) (initial : IRState)
    (fn : IRFunction)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = some fn)
    (guarded : (!fn.payable && tx.msgValue % Constants.evmModulus != 0) = true) :
    exactEmptyRevert (interpretIR contract tx initial) initial := by
  simp [interpretIR, exactEmptyRevert, selected, guarded]

theorem short_args (contract : IRContract) (tx : IRTransaction) (initial : IRState)
    (fn : IRFunction)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = some fn)
    (guarded : (!fn.payable && tx.msgValue % Constants.evmModulus != 0) = false)
    (short : ¬ fn.params.length ≤ tx.args.length) :
    exactEmptyRevert (interpretIR contract tx initial) initial := by
  simp [interpretIR, exactEmptyRevert, selected, guarded, short]

theorem unknown_with_helpers (contract : IRContract) (fuel : Nat) (tx : IRTransaction) (initial : IRState)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = none) :
    exactEmptyRevert (interpretIRWithInternals contract fuel tx initial) initial := by
  simp [interpretIRWithInternals, exactEmptyRevert, selected]

theorem nonpayable_with_helpers (contract : IRContract) (fuel : Nat) (tx : IRTransaction) (initial : IRState)
    (fn : IRFunction)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = some fn)
    (guarded : (!fn.payable && tx.msgValue % Constants.evmModulus != 0) = true) :
    exactEmptyRevert (interpretIRWithInternals contract fuel tx initial) initial := by
  simp [interpretIRWithInternals, exactEmptyRevert, selected, guarded]

theorem short_args_with_helpers (contract : IRContract) (fuel : Nat) (tx : IRTransaction) (initial : IRState)
    (fn : IRFunction)
    (selected : contract.functions.find? (·.selector == tx.functionSelector) = some fn)
    (guarded : (!fn.payable && tx.msgValue % Constants.evmModulus != 0) = false)
    (short : ¬ fn.params.length ≤ tx.args.length) :
    exactEmptyRevert (interpretIRWithInternals contract fuel tx initial) initial := by
  simp [interpretIRWithInternals, exactEmptyRevert, selected, guarded, short]

end SolidityImportSmoke.DispatcherRevertChecks
