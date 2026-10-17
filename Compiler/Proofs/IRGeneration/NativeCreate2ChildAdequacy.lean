import Compiler.Proofs.IRGeneration.NativeCreate2ChildFrame

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul
open Verity.Core.Model.MidnightInitcode

/-- Derive completion of the exact native CREATE2 child invocation, at all
target states and gas budgets. This excludes the swallowed-error map branch. -/
theorem native_create2_child_completed (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (pre : EVM.State) (cost : Nat) (offset size salt : UInt256)
    (code : pre.memory.readWithPadding offset.toNat size.toNat = initcode payload)
    (fuel : Nat) (enough : 10 ≤ fuel) :
    ∃ result, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result := by
  unfold nativeCreate2Child
  dsimp only
  rw [code]
  exact lambda_all_targets_completed payload bounded _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fuel enough


/-- Derive the actual child result and all parent-state frames together;
there is no supplied child-completion certificate in this statement. -/
theorem native_create2_completed_frame (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (fuel cost : Nat) (pre next : EVM.State) (rest : Stack UInt256) (offset size salt : UInt256)
    (enough : 10 ≤ fuel) (code : pre.memory.readWithPadding offset.toNat size.toNat = initcode payload)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152)
    (stepped : EVM.step (fuel + 3) cost (some (.CREATE2, none)) pre = .ok next) :
    ∃ result, nativeCreate2Child (fuel + 2) cost pre offset size salt = .ok result ∧
      next.accountMap = result.2.2.1 ∧ next.substate = result.2.2.2.2.1 ∧ next.createdAccounts = result.2.1 ∧
      next.executionEnv = pre.executionEnv ∧ next.σ₀ = pre.σ₀ ∧ next.memory = pre.memory := by
  obtain ⟨result, completed⟩ := native_create2_child_completed payload bounded pre cost offset size salt code fuel enough
  refine ⟨result, completed, ?_⟩
  exact native_create2_child_frame (fuel + 2) cost pre next rest offset size salt result
    popped nonce entry completed stepped

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
