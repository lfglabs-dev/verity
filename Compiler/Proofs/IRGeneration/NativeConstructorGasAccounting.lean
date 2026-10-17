import Compiler.Proofs.IRGeneration.NativeConstructorDataRun

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

/-- A successful native gas check rules out UInt256 subtraction wrapping. -/
theorem gas_sub_toNat (gas : UInt256) (cost : Nat) (enough : cost ≤ gas.toNat) :
    (gas - UInt256.ofNat cost).toNat = gas.toNat - cost := by
  have bounded : cost < UInt256.size := lt_of_le_of_lt enough gas.val.isLt
  have value : (UInt256.ofNat cost).val.val = cost := Nat.mod_eq_of_lt bounded
  change (gas.val - (UInt256.ofNat cost).val).val = gas.val.val - cost
  rw [Fin.sub_val_of_le (by change (UInt256.ofNat cost).val.val ≤ gas.val.val; rw [value]; exact enough)]
  rw [value]

/-- Z's exact memory debit and instruction charge, with both real guards.
This theorem applies to the actual native Z, including all other rejection
checks, and does not replace those checks by a gas-only approximation. -/
theorem checked_gas (jumps : Array UInt256) (instruction : Operation .EVM)
    (pre mid : EVM.State) (cost : Nat)
    (checked : Z jumps instruction pre = .ok (mid, cost)) :
    mid.gasAvailable.toNat + EVM.memoryExpansionCost pre instruction = pre.gasAvailable.toNat ∧
      cost = EVM.C' mid instruction ∧ cost ≤ mid.gasAvailable.toNat := by
  have frame := Z_ok_state checked
  have body := checked
  simp only [Z, Bind.bind, Except.bind, pure, Except.pure] at body
  have memoryEnough := Nat.le_of_not_lt (elim_guard_not body)
  replace body := elim_guard body
  have instructionEnough := Nat.le_of_not_lt (elim_guard_not body)
  repeat replace body := elim_guard body
  have pair := Except.ok.inj body
  have costEq := congrArg (fun x => x.2) pair
  dsimp only at costEq
  refine ⟨?_, ?_, ?_⟩
  · rw [frame]
    change (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre instruction)).toNat +
      EVM.memoryExpansionCost pre instruction = pre.gasAvailable.toNat
    rw [gas_sub_toNat _ _ memoryEnough]
    omega
  · rw [frame]
    exact costEq.symm
  · rw [frame, ← costEq]
    exact instructionEnough

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
