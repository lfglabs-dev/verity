import Compiler.Proofs.IRGeneration.NativeSourceEmptyRevert

namespace Compiler.Proofs.IRGeneration.NativeSourceRejectionChecks
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups

theorem push0 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 2 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat) (stack : pre.stack.length < 1024) :
    Z jumps (.Push .PUSH0) pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 2) := by
  have cost (state : EVM.State) : C' state (.Push .PUSH0) = 2 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

theorem dup1 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat) (stack : 0 < pre.stack.length ∧ pre.stack.length < 1024) :
    Z jumps (.DUP1) pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state (.DUP1) = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

theorem word_roundtrip (word : UInt256) : UInt256.ofNat word.toNat = word := by
  cases word with
  | mk value =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt value.isLt

theorem revert_memory_cost (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail) :
    memoryExpansionCost pre .REVERT = 0 := by
  simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', stack]
  change Cₘ (UInt256.ofNat pre.activeWords.toNat) - Cₘ pre.activeWords = 0
  rw [word_roundtrip, Nat.sub_self]

theorem zero_revert (jumps : Array UInt256) (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail)
    (depth : tail.length ≤ 1022) :
    Z jumps .REVERT pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 0) := by
  have cost (state : EVM.State) : C' state .REVERT = 0 := by rfl
  simp only [Z, W, revert_memory_cost pre tail stack, cost, Nat.not_lt_zero, if_false]
  simp [δ, α, stack, Operation.isCreate, show ¬1024 < tail.length by omega, show ¬tail.length + 1 + 1 < 2 by omega]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceRejectionChecks
