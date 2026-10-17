import Compiler.Proofs.IRGeneration.NativeConstructorCanonicalReservation

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open NativeCreationWorld
open Verity.Core.Model.Create2Accounts
open Verity.Core.Model.Create2Runtime

/-- Compose the native reservation and actual code insertion with canonical
commit/rollback for either flag. The actual Lambda result must supply that flag;
the creator bump survives rollback. -/
theorem constructor_canonical_commit (machine : EVM.State) (before : Accounts)
    (sender target : AccountAddress) (entry : Account .EVM) (payload : ByteArray)
    (committed : Bool) (present : machine.accountMap.get? sender = some entry)
    (nonce : (machine.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (code : (machine.accountMap.getD target default).code.size = 0)
    (agrees : ∀ owner : AccountAddress,
      bumpCreator before sender.val owner.val = creationAccount machine owner) :
    let entered := constructorEnteredAccounts machine.accountMap sender target (UInt256.ofNat 0)
    ∃ after, reserve before sender.val target.val = .reserved after ∧
      ∀ query : AccountAddress,
        creationAccount { machine with accountMap := (if committed then
          entered.insert target { (entered.getD target default) with code := payload }
          else machine.accountMap) } query =
        (if committed then installRuntime after target.val payload
          else bumpCreator before sender.val) query.val := by
  obtain ⟨after, reserved, projection⟩ := constructor_canonical_reservation
    machine before sender target entry present nonce code agrees
  refine ⟨after, reserved, ?_⟩
  intro query
  cases committed with
  | false => exact (agrees query).symm
  | true =>
      exact constructor_canonical_install
        { machine with accountMap := constructorEnteredAccounts machine.accountMap sender target (UInt256.ofNat 0) }
        after target query payload (fun owner => (projection owner).symm)


/-- Actual completed native Lambda commits the canonical reserved/runtime map
or restores the already-bumped creator map according to its own result flag. -/
theorem lambda_canonical_accounts (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (machine : EVM.State) (before : Accounts) (sender origin : AccountAddress)
    (gas price depth : UInt256) (salt : ByteArray) (permission : Bool)
    (entry : Account .EVM) (present : machine.accountMap.get? sender = some entry)
    (vacant : let target := nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload)
      (machine.accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      (machine.accountMap.getD target default).code.size = 0)
    (agrees : ∀ owner : AccountAddress,
      bumpCreator before sender.val owner.val = creationAccount machine owner)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload)
    ∃ result after,
      EVM.Lambda (fuel + 2) machine.executionEnv.blobVersionedHashes machine.createdAccounts
        machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀ machine.substate
        sender origin gas price (UInt256.ofNat 0) (Verity.Core.Model.MidnightInitcode.initcode payload)
        depth (some salt) machine.executionEnv.header permission = .ok result ∧
      reserve before sender.val target.val = .reserved after ∧
      ∀ query : AccountAddress,
        creationAccount { machine with accountMap := result.2.2.1 } query =
          (if result.2.2.2.2.2.1 then installRuntime after target.val payload
            else bumpCreator before sender.val) query.val := by
  obtain ⟨result, completed, accounts⟩ := lambda_accounts payload bounded
    machine.executionEnv.blobVersionedHashes machine.createdAccounts machine.genesisBlockHeader
    machine.blocks machine.accountMap machine.σ₀ machine.substate sender origin gas price
    (UInt256.ofNat 0) depth salt machine.executionEnv.header permission fuel enough
  obtain ⟨after, reserved, projection⟩ := constructor_canonical_commit machine before sender
    (nativeCreate2Target sender salt (Verity.Core.Model.MidnightInitcode.initcode payload))
    entry payload result.2.2.2.2.2.1 present vacant.1 vacant.2 agrees
  refine ⟨result, after, completed, reserved, ?_⟩
  intro query
  rw [accounts]
  exact projection query

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
