import Compiler.Proofs.IRGeneration.NativeCreationWorld

/-! Frame laws for the actual pinned native storage primitives. These do not
assert opcode permission/gas correctness or a canonical/source-world relation.
The executor must first establish its exceptional prechecks and then connect
these effects to the full world agreement, including source storage channels. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationWorldSteps
open EvmYul

/-- SSTORE retains the transaction's original storage, environment, existing
raw logs and account warmth while updating current storage/refunds/key warmth. -/
theorem sstore_frame (state : EvmYul.State .EVM) (slot value : UInt256) :
    let after := state.sstore slot value
    after.σ₀ = state.σ₀ ∧ after.executionEnv = state.executionEnv ∧
      after.substate.logSeries = state.substate.logSeries ∧
      after.substate.accessedAccounts = state.substate.accessedAccounts := by
  dsimp only
  unfold EvmYul.State.sstore
  cases lookup : state.lookupAccount state.executionEnv.codeOwner with
  | none => simp only [lookup, Option.option]; trivial
  | some account =>
      simp only [lookup, Option.option, EvmYul.State.setAccount,
        EvmYul.State.addAccessedStorageKey, Substate.addAccessedStorageKey]
      trivial

/-- TSTORE does not alter original storage, environment or any access/refund/log
bookkeeping. Transient writes must not be confused with persistent writes. -/
theorem tstore_frame (state : EvmYul.State .EVM) (slot value : UInt256) :
    let after := state.tstore slot value
    after.σ₀ = state.σ₀ ∧ after.executionEnv = state.executionEnv ∧
      after.substate = state.substate := by
  dsimp only
  unfold EvmYul.State.tstore
  cases lookup : state.lookupAccount state.executionEnv.codeOwner with
  | none => simp only [lookup, Option.option]; trivial
  | some account =>
      simp only [lookup, Option.option, EvmYul.State.updateAccount]
      trivial

/-- The actual primitive installs the updated current storage in the actual
account map. Presence is explicit; a zero-valued account view is insufficient. -/
theorem sstore_account (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    (state.sstore slot value).accountMap =
      state.accountMap.insert state.executionEnv.codeOwner (entry.updateStorage slot value) := by
  simp only [EvmYul.State.sstore, present, Option.option, EvmYul.State.setAccount,
    EvmYul.State.addAccessedStorageKey, Substate.addAccessedStorageKey]

/-- Transient writes update the actual account's transient map, not persistent
storage or an observer-only shadow state. -/
theorem tstore_account (state : EvmYul.State .EVM) (slot value : UInt256)
    (entry : Account .EVM)
    (present : state.lookupAccount state.executionEnv.codeOwner = some entry) :
    (state.tstore slot value).accountMap =
      state.accountMap.insert state.executionEnv.codeOwner (entry.updateTransientStorage slot value) := by
  simp only [EvmYul.State.tstore, present, Option.option, EvmYul.State.updateAccount]

end Compiler.Proofs.IRGeneration.NativeCreationWorldSteps
