import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocationDecodes

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoadCheck
open EvmYul EVM EVM.Proof

def expanded (pre : EVM.State) : EVM.State :=
  { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (memoryExpansionCost pre .MLOAD) }

theorem expansion_gas (pre : EVM.State)
    (enough : memoryExpansionCost pre .MLOAD ≤ pre.gasAvailable.toNat) :
    (expanded pre).gasAvailable.toNat = pre.gasAvailable.toNat - memoryExpansionCost pre .MLOAD := by
  have bound : pre.gasAvailable.toNat < 2^256 := pre.gasAvailable.val.isLt
  exact NativeSourceCheckedRejection.gas_sub _ _ (by omega) enough

theorem mload (jumps : Array UInt256) (pre : EVM.State)
    (gas : memoryExpansionCost pre .MLOAD + 3 ≤ pre.gasAvailable.toNat)
    (depth : 1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .MLOAD pre = .ok (expanded pre, 3) := by
  have charged := expansion_gas pre (by omega)
  have cost (state : EVM.State) : C' state .MLOAD = 3 := by rfl
  unfold Z
  rw [if_neg (by omega)]
  change (if (expanded pre).gasAvailable.toNat < C' (expanded pre) .MLOAD then _ else _) = _
  rw [cost, if_neg (by omega)]
  simp [δ, α, expanded, W, Operation.isCreate, show ¬pre.stack.length < 1 by omega,
    show ¬pre.stack.length - 1 + 1 > 1024 by omega]
  rfl

theorem load_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 275)
    (stack : pre.stack = UInt256.ofNat 64 :: tail)
    (gas : memoryExpansionCost pre .MLOAD + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1023) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (NativeSourceLoadStep.loaded 3 (expanded pre) (UInt256.ofNat 64) tail) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceArrayAllocationDecodes.decode275]; rfl
  have check := mload jumps pre gas (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (NativeSourceLoadStep.step fuel 3 (expanded pre) _ tail stack) rfl

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoadCheck
