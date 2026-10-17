import Compiler.Proofs.IRGeneration.NativeConstructorWorldAgreement

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Canonical outcome from the computed native flag; this only packages
already-checked reservation and runtime-installation maps. -/
def constructorOutcome (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress)
    (payload : ByteArray) (flag : Bool) : Create2Runtime.Outcome :=
  if flag then .created target.val (Create2Runtime.installRuntime reserved target.val payload)
  else .failed (Create2Accounts.bumpCreator before sender.val) ByteArray.empty

/-- Existing canonical commit supplies exactly the raw world projection used
by native agreement, for either computed child outcome. -/
theorem constructor_outcome_commit (world : Verity.ContractState)
    (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress)
    (payload : ByteArray) (flag : Bool) :
    CreationStorage.commit world (constructorOutcome before reserved sender target payload flag) =
      .ok (constructorCommitWorld world
        (constructorOutcome before reserved sender target payload flag).accounts target payload flag) := by
  have installed : flag = true →
      ((constructorOutcome before reserved sender target payload flag).accounts target.val).code = payload := by
    intro yes
    rw [constructorOutcome, yes]
    exact Create2Runtime.installRuntime_code reserved target.val payload
  have committed := constructor_commit_world world
    (constructorOutcome before reserved sender target payload flag).accounts target payload flag installed
  cases flag <;> exact committed

/-- Raw world agreement instantiated by the real native account-map equation,
canonical reservation map projection, and real parent environment/substate. -/
theorem constructor_outcome_agreement (world : Verity.ContractState) (machine next : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (before reserved : Create2Accounts.Accounts) (sender target : AccountAddress)
    (entry : Account .EVM) (payload : ByteArray) (flag : Bool)
    (present : machine.accountMap.get? sender = some entry)
    (nonce : (machine.accountMap.getD target default).nonce = UInt256.ofNat 0)
    (distinct : machine.executionEnv.codeOwner ≠ target)
    (maps : let entered := constructorEnteredAccounts machine.accountMap sender target (UInt256.ofNat 0)
      next.accountMap = if flag then entered.insert target { (entered.getD target default) with code := payload }
        else machine.accountMap)
    (environment : next.executionEnv = machine.executionEnv)
    (substate : next.substate = machine.substate.addAccessedAccount target)
    (projection : ∀ owner : AccountAddress,
      (if flag then Create2Runtime.installRuntime reserved target.val payload
        else Create2Accounts.bumpCreator before sender.val) owner.val = creationAccount next owner) :
    Agreement (constructorCommitWorld world
      (constructorOutcome before reserved sender target payload flag).accounts target payload flag)
      next (Create2Access.warm warm target.val) := by
  apply constructor_world_agreement world machine next warm agrees _ sender target entry payload flag
    present nonce distinct maps environment substate
  intro owner
  cases flag <;> exact projection owner


/-- Derive the real child result and transport full raw world agreement to
any real parent continuation carrying that child's accounts and substate. -/
theorem lambda_world_transport (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (world : Verity.ContractState) (machine : EVM.State) (before : Create2Accounts.Accounts)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world machine warm)
    (sender origin : AccountAddress) (gas price depth : UInt256) (salt : ByteArray) (permission : Bool)
    (caller : sender = machine.executionEnv.codeOwner) (entry : Account .EVM)
    (present : machine.accountMap.get? sender = some entry)
    (vacant : let target := nativeCreate2Target sender salt (MidnightInitcode.initcode payload)
      (machine.accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      (machine.accountMap.getD target default).code.size = 0)
    (bumped : ∀ owner : AccountAddress, Create2Accounts.bumpCreator before sender.val owner.val = creationAccount machine owner)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target sender salt (MidnightInitcode.initcode payload)
    ∃ result reserved, EVM.Lambda (fuel + 2) machine.executionEnv.blobVersionedHashes machine.createdAccounts
      machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀ machine.substate
      sender origin gas price (UInt256.ofNat 0) (MidnightInitcode.initcode payload)
      depth (some salt) machine.executionEnv.header permission = .ok result ∧
      Create2Accounts.reserve before sender.val target.val = .reserved reserved ∧
      ∀ next : EVM.State, next.accountMap = result.2.2.1 → next.executionEnv = machine.executionEnv →
        next.substate = result.2.2.2.2.1 →
        Agreement (constructorCommitWorld world
          (constructorOutcome before reserved sender target payload result.2.2.2.2.2.1).accounts
          target payload result.2.2.2.2.2.1) next (Create2Access.warm warm target.val) := by
  obtain ⟨result, reserved, completed, reservation, projection⟩ := lambda_canonical_accounts
    payload bounded machine before sender origin gas price depth salt permission entry present vacant bumped fuel enough
  obtain ⟨child, childCompleted, maps⟩ := lambda_accounts payload bounded machine.executionEnv.blobVersionedHashes
    machine.createdAccounts machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀
    machine.substate sender origin gas price (UInt256.ofNat 0) depth salt machine.executionEnv.header permission fuel enough
  have identical : child = result := Except.ok.inj (childCompleted.symm.trans completed)
  subst child
  have formula := completed
  rw [lambda_constructor payload bounded machine.executionEnv.blobVersionedHashes machine.createdAccounts
    machine.genesisBlockHeader machine.blocks machine.accountMap machine.σ₀ machine.substate sender origin
    gas price (UInt256.ofNat 0) depth salt machine.executionEnv.header permission vacant fuel enough] at formula
  have bookkeeping := lambda_result_bookkeeping payload machine.createdAccounts machine.accountMap
    machine.substate sender gas (UInt256.ofNat 0) salt result formula
  refine ⟨result, reserved, completed, reservation, ?_⟩
  intro next nextMap environment nextSubstate
  apply constructor_outcome_agreement world machine next warm agrees before reserved sender _ entry payload
    result.2.2.2.2.2.1 present vacant.1
  · rw [← caller]; exact (constructor_reserved_distinct before sender _ reserved reservation).symm
  · exact nextMap.trans maps
  · exact environment
  · exact nextSubstate.trans bookkeeping.2.2.1
  · intro owner
    rw [← nextMap] at projection
    exact (projection owner).symm

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
