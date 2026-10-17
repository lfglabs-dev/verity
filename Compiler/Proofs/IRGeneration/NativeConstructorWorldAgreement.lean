import Compiler.Proofs.IRGeneration.NativeConstructorWorldEffects

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Explicit canonical commit fields, for composing the existing native
observations. This is not an evaluator or a source execution certificate. -/
def constructorCommitWorld (world : Verity.ContractState) (canonical : Create2Accounts.Accounts)
    (target : AccountAddress) (payload : ByteArray) (flag : Bool) : Verity.ContractState :=
  { (if flag then CreationStorage.clear world target.val else world) with
    creationAccounts := canonical
    codeSize := fun query => if flag && decide (query = target.val) then
      Verity.Core.Uint256.ofNat payload.size else world.codeSize query
    returndata := [] }

/-- The explicit field update above is exactly the existing canonical commit,
when successful runtime installation supplies its actual payload code. -/
theorem constructor_commit_world (world : Verity.ContractState) (canonical : Create2Accounts.Accounts)
    (target : AccountAddress) (payload : ByteArray) (flag : Bool)
    (installed : flag = true → (canonical target.val).code = payload) :
    CreationStorage.commit world (if flag then .created target.val canonical
      else .failed canonical ByteArray.empty) =
      .ok (constructorCommitWorld world canonical target payload flag) := by
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, if_false, CreationStorage.commit, CreationStorage.clearOnSuccess,
        CreationCommit.commit, ByteArray.size_empty, if_true, constructorCommitWorld, Bool.false_and]
  | true =>
      simp only [if_true, CreationStorage.commit, CreationStorage.clearOnSuccess,
        CreationCommit.commit, constructorCommitWorld, installed rfl, Bool.true_and, decide_eq_true_eq]
      rfl

private theorem native_commit_storage (before after : EVM.State)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray) (flag : Bool)
    (present : before.accountMap.get? sender = some entry)
    (nonce : (before.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (maps : let entered := constructorEnteredAccounts before.accountMap sender target (UInt256.ofNat 0)
      after.accountMap = if flag then entered.insert target { (entered.getD target default) with code := payload }
        else before.accountMap) :
    (after.accountMap.getD query default).storage =
      (if flag && decide (query = target) then default else (before.accountMap.getD query default).storage) ∧
    (after.accountMap.getD query default).tstorage = (before.accountMap.getD query default).tstorage := by
  rw [maps]
  exact constructor_commit_storage before.accountMap sender target query entry payload flag present nonce

private theorem native_commit_balance (before after : EVM.State)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray) (flag : Bool)
    (present : before.accountMap.get? sender = some entry)
    (nonce : (before.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (maps : let entered := constructorEnteredAccounts before.accountMap sender target (UInt256.ofNat 0)
      after.accountMap = if flag then entered.insert target { (entered.getD target default) with code := payload }
        else before.accountMap) :
    (creationAccount after query).balance = (creationAccount before query).balance := by
  have effect := constructor_commit_balance before.accountMap sender target query entry payload flag present nonce
  unfold creationAccount account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  rw [maps, effect]

private theorem native_commit_code (before after : EVM.State)
    (sender target query : AccountAddress) (entry : Account .EVM) (payload : ByteArray) (flag : Bool)
    (present : before.accountMap.get? sender = some entry)
    (nonce : (before.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (maps : let entered := constructorEnteredAccounts before.accountMap sender target (UInt256.ofNat 0)
      after.accountMap = if flag then entered.insert target { (entered.getD target default) with code := payload }
        else before.accountMap) :
    (account after query).code = if flag && decide (query = target) then payload else (account before query).code := by
  have effect := constructor_commit_code before.accountMap sender target query entry payload flag present nonce
  unfold account account?
  simp only [Std.TreeMap.get?_eq_getElem?, ← Std.TreeMap.getD_eq_getD_getElem?]
  rw [maps]
  exact effect

private theorem commit_world_codeSizes (world : Verity.ContractState) (before after : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (canonical : Create2Accounts.Accounts) (target : AccountAddress) (payload : ByteArray) (flag : Bool)
    (codes : ∀ owner : AccountAddress, (account after owner).code =
      if flag && decide (owner = target) then payload else (account before owner).code) :
    ∀ owner : AccountAddress, (constructorCommitWorld world canonical target payload flag).codeSize owner.val =
      Verity.Core.Uint256.ofNat (account after owner).code.size := by
  intro owner
  rw [codes owner]
  unfold constructorCommitWorld
  by_cases same : owner = target
  · subst owner
    cases flag with
    | false => exact agrees.codeSizes target
    | true => simp only [decide_true, Bool.and_self, if_true]
  · have values : owner.val ≠ target.val := fun equal => same (Fin.ext equal)
    simp only [same, values, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
    exact agrees.codeSizes owner

/-- Compose all raw world fields from actual native map/environment/substate
updates. Source typed channels and execution provenance remain separate. -/
theorem constructor_world_agreement (world : Verity.ContractState) (before after : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world before warm)
    (canonical : Create2Accounts.Accounts) (sender target : AccountAddress)
    (entry : Account .EVM) (payload : ByteArray) (flag : Bool)
    (present : before.accountMap.get? sender = some entry)
    (nonce : (before.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (distinct : before.executionEnv.codeOwner ≠ target)
    (maps : let entered := constructorEnteredAccounts before.accountMap sender target (UInt256.ofNat 0)
      after.accountMap = if flag then entered.insert target { (entered.getD target default) with code := payload }
        else before.accountMap)
    (environment : after.executionEnv = before.executionEnv)
    (substate : after.substate = before.substate.addAccessedAccount target)
    (projection : ∀ owner : AccountAddress, canonical owner.val = creationAccount after owner) :
    Agreement (constructorCommitWorld world canonical target payload flag) after
      (Create2Access.warm warm target.val) := by
  have storage := native_commit_storage before after sender target
  have balance := native_commit_balance before after sender target
  have code := native_commit_code before after sender target
  refine ⟨?_, ?_, ?_, ?_, projection, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [environment]; cases flag <;> exact agrees.caller
  · rw [environment]; cases flag <;> exact agrees.source
  · rw [environment]; cases flag <;> exact agrees.origin
  · rw [environment]; cases flag <;> exact agrees.value
  · rw [environment, balance before.executionEnv.codeOwner entry payload flag present nonce maps]
    cases flag <;> exact agrees.selfBalance
  · exact commit_world_codeSizes world before after warm agrees canonical target payload flag
      (fun owner => code owner entry payload flag present nonce maps)
  · intro slot
    rw [environment]
    exact constructor_caller_persistent world before after warm agrees target flag slot distinct
      (storage before.executionEnv.codeOwner entry payload flag present nonce maps).1
  · intro slot
    rw [environment]
    exact constructor_caller_transient world before after warm agrees target flag slot
      (storage before.executionEnv.codeOwner entry payload flag present nonce maps).2
  · intro owner foreign slot
    rw [environment] at foreign
    exact constructor_parked_persistent world before after warm agrees target owner flag slot foreign
      (storage owner entry payload flag present nonce maps).1
  · intro owner foreign slot
    rw [environment] at foreign
    exact constructor_parked_transient world before after warm agrees target owner flag slot foreign
      (storage owner entry payload flag present nonce maps).2
  · intro owner
    change Create2Access.warm warm target.val owner.val = after.substate.accessedAccounts.contains owner
    rw [substate]
    exact constructor_access_projection before warm target owner agrees.accountAccess

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
