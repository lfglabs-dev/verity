import Compiler.Proofs.IRGeneration.NativeSourceMidnightFieldStore

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldStoreChecks
open EvmYul EVM EVM.Proof EVM.InstructionGasGroups

theorem dup4 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 4 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP4 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP4 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 4 by omega, show ¬pre.stack.length - 4 + 5 > 1024 by omega]

theorem dup2 (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1023) :
    Z jumps .DUP2 pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .DUP2 = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 + 3 > 1024 by omega]

theorem add (jumps : Array UInt256) (pre : EVM.State)
    (gas : 3 ≤ (pre.gasAvailable - UInt256.ofNat 0).toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .ADD pre = .ok ({ pre with gasAvailable := pre.gasAvailable - UInt256.ofNat 0 }, 3) := by
  have cost (state : EVM.State) : C' state .ADD = 3 := by rfl
  simp only [Z, W, memoryExpansionCost, memoryExpansionCost.μᵢ', Nat.sub_self, cost]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [δ, α, Option.getD_some, Operation.isCreate, reduceIte, reduceCtorEq, false_and, Bind.bind, Except.bind,
    pure, Except.pure]
  simp [show ¬pre.stack.length < 2 by omega, show ¬pre.stack.length - 2 + 1 > 1024 by omega]

def expanded (pre : EVM.State) : EVM.State :=
  { pre with gasAvailable := pre.gasAvailable - UInt256.ofNat (memoryExpansionCost pre .MSTORE) }

theorem expansion_gas (pre : EVM.State)
    (enough : memoryExpansionCost pre .MSTORE ≤ pre.gasAvailable.toNat) :
    (expanded pre).gasAvailable.toNat = pre.gasAvailable.toNat - memoryExpansionCost pre .MSTORE := by
  have bound : pre.gasAvailable.toNat < 2 ^ 256 := pre.gasAvailable.val.isLt
  exact NativeSourceCheckedRejection.gas_sub _ _ (by omega) enough

theorem mstore (jumps : Array UInt256) (pre : EVM.State)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat)
    (depth : 2 ≤ pre.stack.length ∧ pre.stack.length ≤ 1024) :
    Z jumps .MSTORE pre = .ok (expanded pre, 3) := by
  have charged := expansion_gas pre (by omega)
  have cost (state : EVM.State) : C' state .MSTORE = 3 := by rfl
  unfold Z
  rw [if_neg (by omega)]
  change (if (expanded pre).gasAvailable.toNat < C' (expanded pre) .MSTORE then _ else _) = _
  rw [cost, if_neg (by omega)]
  simp [δ, α, expanded, W, Operation.isCreate, show ¬pre.stack.length < 2 by omega,
    show ¬pre.stack.length - 2 > 1024 by omega]
  rfl

theorem store_continue (fuel : Nat) (jumps : Array UInt256) (pre : EVM.State)
    (offset word : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 198)
    (stack : pre.stack = offset :: word :: tail)
    (gas : memoryExpansionCost pre .MSTORE + 3 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) jumps pre =
      EVM.X (fuel + 1) jumps (mstorePost 3 (expanded pre) tail offset word) := by
  have decoded : decodeAt pre = (.MSTORE, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceMidnightFieldStore.decode198]; rfl
  have check := mstore jumps pre gas (by simp only [stack, List.length_cons]; omega)
  exact X_succ_of_continue decoded check (step_MSTORE fuel 3 (expanded pre) tail offset word
    (by change pre.stack.pop2 = _; rw [stack]; rfl)) rfl

end Compiler.Proofs.IRGeneration.NativeSourceFieldStoreChecks
