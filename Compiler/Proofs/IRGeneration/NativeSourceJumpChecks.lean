import Compiler.Proofs.IRGeneration.NativeSourceJumpDestinations
import Compiler.Proofs.IRGeneration.NativeSourceCheckedRejection

namespace Compiler.Proofs.IRGeneration.NativeSourceJumpChecks
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups

theorem contains_of_mem (jumps : Array UInt256) (destination : UInt256)
    (present : destination ∈ jumps) : jumps.contains destination = true := by
  apply Array.contains_iff_exists_mem_beq.mpr
  refine ⟨destination, present, ?_⟩
  change (destination.val == destination.val) = true
  simp

theorem rejection_contains :
    (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 91) = true := by
  exact contains_of_mem _ _ NativeSourceJumpDestinations.rejection_destination

theorem rejection_notIn (condition : UInt256) (tail : Stack UInt256) :
    EVM.X.notIn ((UInt256.ofNat 91 :: condition :: tail)[0]?)
      (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) = false := by
  change (!(EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)).contains (UInt256.ofNat 91)) = false
  rw [rejection_contains]
  rfl

theorem jumpi (jumps : Array UInt256) (pre : EVM.State)
    (gas : 10 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (stack : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024)
    (destination : EVM.X.notIn pre.stack[0]? jumps = false) :
    Z jumps .JUMPI pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 10) := by
  have cost (state : EVM.State) : C' state .JUMPI = 10 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [destination, show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 > 1024 by omega]

theorem rejection_jumpi (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail)
    (gas : 10 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : tail.length ≤ 1022) :
    Z (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) .JUMPI pre =
      .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 10) := by
  apply jumpi _ pre gas
  · simp only [stack, List.length_cons]; omega
  · rw [stack]
    exact rejection_notIn condition tail

end Compiler.Proofs.IRGeneration.NativeSourceJumpChecks
