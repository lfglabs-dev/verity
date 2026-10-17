import Compiler.Proofs.IRGeneration.NativeCreate2ChildAdequacy

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- The parent state passed into native Lambda, after cost and nonce updates. -/
def create2ChildEntry (pre : EVM.State) (cost : Nat) : EVM.State :=
  creatorBumpedMachine { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
    pre.executionEnv.codeOwner

private theorem commit_world_bumped (world : Verity.ContractState) (before canonical : Create2Accounts.Accounts)
    (sender target : AccountAddress) (payload : ByteArray) (flag : Bool) :
    constructorCommitWorld (world.withCreationAccounts (Create2Accounts.bumpCreator before sender.val))
      canonical target payload flag = constructorCommitWorld world canonical target payload flag := by
  cases flag <;> rfl

/-- Derive the real child and full world transport at the exact CREATE2 entry.
No account agreement after the nonce bump is supplied as an extra premise. -/
theorem native_create2_child_world (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ result reserved, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      Create2Accounts.reserve world.creationAccounts pre.executionEnv.codeOwner.val target.val = .reserved reserved ∧
      ∀ next : EVM.State, next.accountMap = result.2.2.1 → next.executionEnv = pre.executionEnv →
        next.substate = result.2.2.2.2.1 →
        Agreement (constructorCommitWorld world (constructorOutcome world.creationAccounts reserved
          pre.executionEnv.codeOwner target payload result.2.2.2.2.2.1).accounts
          target payload result.2.2.2.2.2.1) next (Create2Access.warm warm target.val) := by
  let charged := { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat cost }
  have chargedAgreement := agreement_local world pre warm agrees charged.gasAvailable pre.pc pre.stack pre.memory
  have bound : (charged.accountMap.getD pre.executionEnv.codeOwner default).nonce.toNat + 1 < UInt256.size := by
    apply creator_bump_nonce_bound
    simpa only [Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?] using nonce
  have bumpedAgreement := creator_bump_world_agreement world charged warm chargedAgreement pre.executionEnv.codeOwner bound
  obtain ⟨result, reserved, completed, reservation, transport⟩ := lambda_world_transport payload bounded
    (world.withCreationAccounts (Create2Accounts.bumpCreator world.creationAccounts pre.executionEnv.codeOwner.val))
    (create2ChildEntry pre cost) world.creationAccounts warm bumpedAgreement pre.executionEnv.codeOwner
    pre.executionEnv.sender (UInt256.ofNat (EVM.L charged.gasAvailable.toNat)) (UInt256.ofNat pre.executionEnv.gasPrice)
    (UInt256.ofNat (pre.executionEnv.depth + 1)) salt.toByteArray pre.executionEnv.perm rfl _
    (creator_bump_present charged pre.executionEnv.codeOwner) vacant
    (constructor_creator_bump charged world.creationAccounts pre.executionEnv.codeOwner · bound agrees.accounts) fuel enough
  refine ⟨result, reserved, ?_, reservation, ?_⟩
  · simpa only [nativeCreate2Child, create2ChildEntry, creatorBumpedMachine, charged, code] using completed
  · intro next maps environment substate
    have agreement := transport next maps environment substate
    rw [commit_world_bumped] at agreement
    exact agreement


/-- Raw world agreement for the actual successful native CREATE2 instruction,
using its real child result and the existing canonical storage-world commit. -/
theorem native_create2_world_agreement (world : Verity.ContractState) (pre next : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (payload : ByteArray) (bounded : payload.size ≤ 49152) (fuel cost : Nat)
    (rest : Stack UInt256) (offset size salt : UInt256) (enough : 10 ≤ fuel)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = MidnightInitcode.initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (vacant : let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
      ((create2ChildEntry pre cost).accountMap.getD target default).nonce = UInt256.ofNat 0 ∧
      ((create2ChildEntry pre cost).accountMap.getD target default).code.size = 0)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ result reserved committed, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      CreationStorage.commit world (constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner
        target payload result.2.2.2.2.2.1) = .ok committed ∧
      Agreement committed next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨result, reserved, completed, _, transport⟩ := native_create2_child_world
    world pre warm agrees payload bounded cost offset size salt code nonce vacant fuel enough
  have frames := native_create2_child_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry completed stepped
  let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
  refine ⟨result, reserved, _, completed,
    constructor_outcome_commit world world.creationAccounts reserved pre.executionEnv.codeOwner target payload result.2.2.2.2.2.1,
    transport next frames.1 frames.2.2.2.1 frames.2.1, frames.2.2.2.2.1, frames.2.2.2.2.2⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
