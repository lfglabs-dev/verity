import Compiler.Proofs.IRGeneration.NativeSourceCollateralSpan

namespace Compiler.Proofs.IRGeneration.NativeSourceSpanChecks
open EvmYul EVM EVM.Proof

theorem calldatasize (jumps : Array UInt256) (pre : EVM.State)
    (gas : 2 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 0 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .CALLDATASIZE pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 2) := by
  have cost (state : EVM.State) : C' state .CALLDATASIZE = 2 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [depth.2]

theorem slt (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .SLT pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .SLT = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 + 1 > 1024 by omega]

theorem iszero (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 1 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .ISZERO pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .ISZERO = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 1 by omega, show ¬pre.stack.length - 1 + 1 > 1024 by omega]

end Compiler.Proofs.IRGeneration.NativeSourceSpanChecks
