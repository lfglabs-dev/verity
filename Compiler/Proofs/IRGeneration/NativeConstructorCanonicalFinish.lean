import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalCommit

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open NativeCreationWorld
open Verity.Core.Model.Create2Accounts
open Verity.Core.Model.Create2Runtime
open Verity.Core.Model.Create2Callee
open Verity.Core.Model.MidnightInitcode

/-- Canonical completion for the exact computed native flag. Runtime acceptance
must be established on success; no acceptance premise is needed on rollback. -/
theorem constructor_canonical_finish (before after : Accounts) (sender target : Nat)
    (payload : ByteArray) (flag : Bool)
    (reserved : reserve before sender target = .reserved after)
    (accepted : flag = true → runtimeAccepted payload = true) :
    finish before sender target (if flag then .returned payload true else .exceptional) =
      if flag then .created target (installRuntime after target payload)
      else .failed (bumpCreator before sender) ByteArray.empty := by
  cases flag with
  | false => exact finish_exceptional before sender target after reserved
  | true => exact finish_returned before sender target after reserved payload (accepted rfl)

/-- Transport the canonical computed callee result through reserve and finish,
retaining the native gas and exact commit/rollback account map. -/
theorem constructor_canonical_entered (before after : Accounts) (sender target : Nat)
    (payload : ByteArray) (gas remaining : Nat) (flag : Bool)
    (reserved : reserve before sender target = .reserved after)
    (executed : execute payload gas = .ok
      { result := if flag then .returned payload true else .exceptional, gasLeft := remaining })
    (accepted : flag = true → runtimeAccepted payload = true) :
    runEntered before sender target payload gas = .ok
      { outcome := if flag then .created target (installRuntime after target payload)
          else .failed (bumpCreator before sender) ByteArray.empty
        gasLeft := remaining } := by
  simp only [runEntered, reserved, executed]
  rw [constructor_canonical_finish before after sender target payload flag reserved accepted]


private theorem execute_flag_accepted (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (gas remaining : Nat) (flag : Bool)
    (executed : execute payload gas = .ok
      { result := if flag then .returned payload true else .exceptional, gasLeft := remaining })
    (yes : flag = true) : runtimeAccepted payload = true := by
  have large : 49163 < modulus := by decide
  have nowrap : 11 + payload.size < modulus := by omega
  rw [yes, execute_formula payload nowrap gas] at executed
  split at executed
  · next funded => exact (Bool.and_eq_true_iff.mp funded).1
  · cases executed

/-- Actual native Lambda and canonical runEntered agree on the computed child
outcome, remaining gas and every real account view, including failed deposit. -/
theorem lambda_canonical_entered (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (machine : EVM.State) (before : Accounts) (sender origin : AccountAddress)
    (gas price depth : UInt256) (salt : ByteArray) (permission : Bool)
    (entry : Account .EVM) (present : machine.accountMap.get? sender = some entry)
    (vacant : let target := nativeCreate2Target sender salt (initcode payload)
      (machine.accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      (machine.accountMap.getD target default).code.size = 0)
    (agrees : ∀ owner : AccountAddress,
      bumpCreator before sender.val owner.val = creationAccount machine owner)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (initcode payload)
    ∃ result outcome,
      EVM.Lambda (fuel + 2) machine.executionEnv.blobVersionedHashes machine.createdAccounts
        machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀ machine.substate
        sender origin gas price (UInt256.ofNat 0) (initcode payload)
        depth (some salt) machine.executionEnv.header permission = .ok result ∧
      runEntered before sender.val target.val payload gas.toNat =
        .ok { outcome := outcome, gasLeft := result.2.2.2.1.toNat } ∧
      (∀ query : AccountAddress, creationAccount { machine with accountMap := result.2.2.1 } query =
        outcome.accounts query.val) ∧
      (match outcome with | .created _ _ => true | .failed _ _ => false) = result.2.2.2.2.2.1 ∧
      result.2.2.2.2.2.2 = ByteArray.empty := by
  obtain ⟨result, after, completed, reserved, projection⟩ := lambda_canonical_accounts
    payload bounded machine before sender origin gas price depth salt permission entry present vacant agrees fuel enough
  obtain ⟨child, childCompleted, executed, empty⟩ := lambda_canonical_callee payload bounded
    machine.executionEnv.blobVersionedHashes machine.createdAccounts machine.genesisBlockHeader
    machine.blocks machine.accountMap machine.σ₀ machine.substate sender origin gas price
    (UInt256.ofNat 0) depth salt machine.executionEnv.header permission vacant fuel enough
  have identical : child = result := Except.ok.inj (childCompleted.symm.trans completed)
  subst child
  have accepted := execute_flag_accepted payload bounded gas.toNat result.2.2.2.1.toNat
    result.2.2.2.2.2.1 executed
  let target := nativeCreate2Target sender salt (initcode payload)
  let outcome : Outcome := if result.2.2.2.2.2.1 then
    .created target.val (installRuntime after target.val payload)
    else .failed (bumpCreator before sender.val) ByteArray.empty
  refine ⟨result, outcome, completed, ?_, ?_, ?_, empty⟩
  · exact constructor_canonical_entered before after sender.val target.val payload gas.toNat
      result.2.2.2.1.toNat result.2.2.2.2.2.1 reserved executed accepted
  · intro query
    rw [projection query]
    dsimp only [outcome]
    split <;> rfl
  · dsimp only [outcome]
    cases result.2.2.2.2.2.1 <;> rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
