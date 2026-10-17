import Compiler.Proofs.IRGeneration.NativeConstructorGasStages

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

private theorem step_gas_extent {fuel cost : Nat} {instruction : Instruction}
    {pre post expected : EVM.State} {words : UInt256}
    (specified : StepOk fuel cost instruction pre expected)
    (success : EVM.step fuel cost (some instruction) pre = .ok post)
    (gas : expected.gasAvailable = pre.gasAvailable - UInt256.ofNat cost)
    (extent : expected.activeWords = words) :
    post.gasAvailable = pre.gasAvailable - UInt256.ofNat cost ∧ post.activeWords = words := by
  have same := Except.ok.inj (specified.symm.trans success)
  subst post
  exact ⟨gas, extent⟩

/-- Exact gas and memory extent after any continuing constructor stage. -/
theorem data_next_gas_extent (payload : ByteArray) (stage : Fin 8)
    (pre post : EVM.State) (fuel gasCost : Nat)
    (holds : DataAt payload ⟨stage.val, by omega⟩ pre)
    (extent : pre.activeWords = UInt256.ofNat (stageWords payload.size ⟨stage.val, by omega⟩))
    (bounded : payload.size < UInt256.size)
    (success : EVM.step (fuel + 1) gasCost
      (some (stageInstruction ⟨stage.val, by omega⟩)) pre = .ok post) :
    post.gasAvailable = pre.gasAvailable - UInt256.ofNat gasCost ∧
      post.activeWords = UInt256.ofNat (stageWords payload.size ⟨stage.val + 1, by omega⟩) := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_gas_extent (step_PUSH1 fuel gasCost pre (.ofNat 11)) success rfl extent
  · exact step_gas_extent (step_CODESIZE fuel gasCost pre) success rfl extent
  · have popped : pre.stack.pop2 = some ([], UInt256.ofNat (11 + payload.size), UInt256.ofNat 11) := by
      rw [holds.2.2.1]; rfl
    exact step_gas_extent (step_SUB fuel gasCost pre [] _ _ popped) success rfl extent
  · exact step_gas_extent (step_DUP1 fuel gasCost pre (.ofNat payload.size) [] holds.2.2.1)
      success rfl extent
  · exact step_gas_extent (step_PUSH1 fuel gasCost pre (.ofNat 11)) success rfl extent
  · exact step_gas_extent (step_PUSH0 fuel gasCost pre) success rfl extent
  · have popped : pre.stack.pop3 = some ([UInt256.ofNat payload.size],
        UInt256.ofNat 0, UInt256.ofNat 11, UInt256.ofNat payload.size) := by
      rw [holds.2.2.1]; rfl
    refine step_gas_extent (step_CODECOPY fuel gasCost pre _ _ _ _ popped) success rfl ?_
    change UInt256.ofNat (MachineState.M pre.activeWords.toNat 0 (UInt256.ofNat payload.size).toNat) = _
    have value : (UInt256.ofNat payload.size).toNat = payload.size := Nat.mod_eq_of_lt bounded
    rw [extent, value]
    exact congrArg UInt256.ofNat (fresh_extent payload.size)
  · exact step_gas_extent (step_PUSH0 fuel gasCost pre) success rfl extent

/-- RETURN debits only its actual instruction charge. -/
theorem data_return_gas (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨8, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.RETURN, none)) pre = .ok post) :
    post.gasAvailable = pre.gasAvailable - UInt256.ofNat gasCost := by
  have popped : pre.stack.pop2 = some ([], UInt256.ofNat 0, UInt256.ofNat payload.size) := by
    rw [holds.2.2.1]; rfl
  have same := Except.ok.inj ((step_RETURN fuel gasCost pre _ _ _ popped).symm.trans success)
  subst post
  rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
