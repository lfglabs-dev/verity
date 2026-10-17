import Compiler.Proofs.IRGeneration.NativeCreate2GasReturn

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Actual entered CREATE2 completes and agrees with an actual canonical
world commit. Neither child nor parent completion is assumed. -/
theorem native_create2_world_completed (world : Verity.ContractState) (pre : EVM.State)
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
    (gasBound : (pre.gasAvailable - UInt256.ofNat cost).toNat < 2^255) :
    let target := nativeCreate2Target pre.executionEnv.codeOwner salt.toByteArray (MidnightInitcode.initcode payload)
    ∃ next result reserved committed,
      EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next ∧
      nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      CreationStorage.commit world (constructorOutcome world.creationAccounts reserved pre.executionEnv.codeOwner
        target payload result.2.2.2.2.2.1) = .ok committed ∧
      Agreement committed next (Create2Access.warm warm target.val) ∧
      next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨next, stepped⟩ := native_create2_parent_completed payload bounded fuel cost pre rest offset size salt
    enough code popped nonce entry gasBound
  obtain ⟨result, reserved, committed, child, commit, agreement, original, memory⟩ :=
    native_create2_world_agreement world pre next warm agrees payload bounded fuel cost rest offset size salt
      enough code popped nonce entry vacant stepped
  exact ⟨next, result, reserved, committed, stepped, child, commit, agreement, original, memory⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
