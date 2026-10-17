import Compiler.Proofs.IRGeneration.SourceSemantics

/-! Canonical public entry rollback retains explicit revert bytes.
The execution premise is the real entry frame, including ABI binding and
contract error declarations; no hypothetical post-world is supplied. -/
namespace Compiler.Proofs.IRGeneration.SourcePublicRevertLaws
open Compiler.CompilationModel SourceSemantics

theorem function_revert_bytes (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome) (bindings : List (String × Nat))
    (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithEvents (effectiveFields spec) spec.events
      { world := withTransactionContext initialWorld tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data) :
    interpretFunction spec fn tx initialWorld oracle =
      { revertedResult spec (withTransactionContext initialWorld tx) with revertData := data } := by
  simp only [interpretFunction, bound, executed]

theorem function_revert_storage_frame (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome) (bindings : List (String × Nat))
    (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithEvents (effectiveFields spec) spec.events
      { world := withTransactionContext initialWorld tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data) :
    (interpretFunction spec fn tx initialWorld oracle).finalStorage =
      encodeStorage spec (withTransactionContext initialWorld tx) := by
  rw [function_revert_bytes spec fn tx initialWorld oracle bindings data bound executed]
  rfl

theorem function_revert_event_frame (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (oracle : Nat → ExternalCallOutcome) (bindings : List (String × Nat))
    (data : List UInt8)
    (bound : bindExternalParams tx.functionSelector fn.bindingParams tx.args = some bindings)
    (executed : execStmtListWithEvents (effectiveFields spec) spec.events
      { world := withTransactionContext initialWorld tx, bindings := bindings,
        selector := tx.functionSelector, externalCallOracle := oracle, errors := spec.errors }
      fn.body = .revertWithData data) :
    (interpretFunction spec fn tx initialWorld oracle).events =
      encodeEvents (withTransactionContext initialWorld tx).events := by
  rw [function_revert_bytes spec fn tx initialWorld oracle bindings data bound executed]
  rfl

end Compiler.Proofs.IRGeneration.SourcePublicRevertLaws
