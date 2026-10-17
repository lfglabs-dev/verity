import Compiler.Proofs.IRGeneration.NativeCreate2CanonicalCollision

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul NativeCreationWorld
open Verity.Core.Model

/-- Exact continued native state when CREATE2 does not enter its child. -/
def create2RejectedState (pre : EVM.State) (cost : Nat) (rest : Stack UInt256)
    (offset size : UInt256) : EVM.State :=
  { pre with
    gasAvailable := pre.gasAvailable - UInt256.ofNat cost
    activeWords := UInt256.ofNat (MachineState.M pre.activeWords.toNat offset.toNat size.toNat)
    returnData := ByteArray.empty
    stack := rest.push (UInt256.ofNat 0)
    pc := pre.pc + UInt256.ofNat 1
    execLength := pre.execLength + 1 }

private theorem forwarded_exact (gas : UInt256) :
    (UInt256.ofNat (EVM.L gas.toNat)).toNat = EVM.L gas.toNat := by
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (native_forwarded_gas_le gas) gas.val.isLt)

private theorem rejected_gas_guard (gas : UInt256) (bounded : gas.toNat < 2^255) :
    ¬ (gas + UInt256.ofNat (EVM.L gas.toNat)).toNat < EVM.L gas.toNat := by
  apply native_parent_gas_guard gas _ bounded
  rw [forwarded_exact]
  exact native_forwarded_gas_le gas

private theorem rejected_gas_refund (gas : UInt256) :
    UInt256.ofNat (gas.toNat - EVM.L gas.toNat + (UInt256.ofNat (EVM.L gas.toNat)).toNat) = gas := by
  rw [forwarded_exact, Nat.sub_add_cancel (native_forwarded_gas_le gas)]
  cases gas with
  | mk value =>
    change UInt256.mk (Fin.ofNat _ value.val) = UInt256.mk value
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt

/-- Native nonce refusal does not execute initcode or increment any nonce.
The native >= guard is retained; canonical larger-than-uint64 refusal is separate. -/
theorem native_create2_nonce_rejected (fuel cost : Nat) (pre : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (bounded : (pre.gasAvailable - UInt256.ofNat cost).toNat < 2^255) :
    EVM.step (fuel + 1) cost (some (.CREATE2, none)) pre =
      .ok (create2RejectedState pre cost rest offset size) := by
  have guard := rejected_gas_guard (pre.gasAvailable - UInt256.ofNat cost) bounded
  simp only [EVM.step]
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  simp only [popped, nonce, if_true]
  rw [if_neg guard, rejected_gas_refund]
  rfl

/-- Native depth/size/value entry refusal never invokes Lambda or bumps nonce.
This is the raw step; outer static/size exceptional prechecks remain separate. -/
theorem native_create2_entry_rejected (fuel cost : Nat) (pre : EVM.State)
    (rest : Stack UInt256) (offset size salt : UInt256)
    (popped : pre.stack.pop4 = some (rest, UInt256.ofNat 0, offset, size, salt))
    (nonce : ¬ ((pre.accountMap.get? pre.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64 - 1)
    (entry : ¬ (UInt256.ofNat 0 ≤ (pre.accountMap.get? pre.executionEnv.codeOwner |>.option (UInt256.ofNat 0) (·.balance)) ∧
      pre.executionEnv.depth < 1024 ∧ (pre.memory.readWithPadding offset.toNat size.toNat).size ≤ 49152))
    (bounded : (pre.gasAvailable - UInt256.ofNat cost).toNat < 2^255) :
    EVM.step (fuel + 1) cost (some (.CREATE2, none)) pre =
      .ok (create2RejectedState pre cost rest offset size) := by
  have guard := rejected_gas_guard (pre.gasAvailable - UInt256.ofNat cost) bounded
  simp only [EVM.step]
  dsimp only [Pure.pure, Except.pure, Bind.bind, Except.bind]
  simp only [popped, nonce, if_false]
  simp only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) by rfl] at entry ⊢
  simp only [entry, if_false]
  rw [if_neg guard, rejected_gas_refund]
  rfl

/-- Refused child entry preserves all raw world fields; only local caller
observations change. This does not assert full canonical entry equivalence. -/
theorem create2_rejected_world (world : Verity.ContractState) (pre : EVM.State)
    (warm : Create2Access.WarmAccounts) (agrees : Agreement world pre warm)
    (cost : Nat) (rest : Stack UInt256) (offset size : UInt256) :
    Agreement world (create2RejectedState pre cost rest offset size) warm := by
  exact agreement_frame_transport world pre _ warm agrees rfl rfl rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
