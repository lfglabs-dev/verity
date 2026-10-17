import Compiler.Proofs.IRGeneration.NativeConstructorGasRun

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

/-- Non-gas guards which are actually valid at each constructor boundary. -/
def SafeLocal (pre : EVM.State) (instruction : Operation .EVM) : Prop :=
  EVM.δ instruction ≠ none ∧ (EVM.δ instruction).getD 0 ≤ pre.stack.length ∧
    pre.stack.length - (EVM.δ instruction).getD 0 + (EVM.α instruction).getD 0 ≤ 1024 ∧
    instruction ≠ .JUMP ∧ instruction ≠ .JUMPI ∧ instruction ≠ .RETURNDATACOPY ∧
    instruction ≠ .SSTORE ∧ W instruction pre.stack = false ∧ instruction.isCreate = false

private theorem stage_safe (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (holds : DataAt payload stage pre) : SafeLocal pre (stageInstruction stage).1 := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [SafeLocal, stageInstruction, holds.2.2.1, stageStack, W, EVM.δ, EVM.α,
    Operation.isCreate]

private theorem local_checks (pre : EVM.State) (instruction : Operation .EVM)
    (jumps : Array UInt256) (safe : SafeLocal pre instruction) :
    Z jumps instruction pre =
      (let mid := zMid pre instruction
       if pre.gasAvailable.toNat < EVM.memoryExpansionCost pre instruction then .error .OutOfGass
       else if mid.gasAvailable.toNat < EVM.C' mid instruction then .error .OutOfGass
       else .ok (mid, EVM.C' mid instruction)) := by
  rcases safe with ⟨valid, stack, limit, jump, jumpi, copy, store, readonly, create⟩
  simp only [Z, zMid, valid, Nat.not_lt.mpr stack, Nat.not_lt.mpr limit, jump, jumpi,
    copy, store, readonly, create, false_and, and_false, if_false, Bool.false_eq_true,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Native Z retains exactly its two gas rejection gates at reachable stages. -/
theorem stage_checks (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (jumps : Array UInt256) (holds : DataAt payload stage pre) :
    Z jumps (stageInstruction stage).1 pre =
      (let instruction := (stageInstruction stage).1
       let mid := zMid pre instruction
       if pre.gasAvailable.toNat < EVM.memoryExpansionCost pre instruction then .error .OutOfGass
       else if mid.gasAvailable.toNat < EVM.C' mid instruction then .error .OutOfGass
       else .ok (mid, EVM.C' mid instruction)) := by
  exact local_checks pre _ jumps (stage_safe payload stage pre holds)

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem stage_budget (size : Nat) (stage : Fin 9) :
    stageSpent size stage + stageCost size stage +
      (if stage.val = 6 then memoryCost (words size) else 0) ≤ prefixCost size := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [stageSpent, stageCost, prefixCost]
  all_goals omega

/-- Enough total constructor gas makes the actual current Z check succeed. -/
theorem checked_of_budget (initial : Nat) (payload : ByteArray) (stage : Fin 9)
    (pre : EVM.State) (jumps : Array UInt256) (holds : GasAt initial payload stage pre)
    (bounded : payload.size ≤ 49152) (enough : prefixCost payload.size ≤ initial) :
    Z jumps (stageInstruction stage).1 pre =
      .ok (zMid pre (stageInstruction stage).1, stageCost payload.size stage) := by
  let instruction := (stageInstruction stage).1
  have dataMid : DataAt payload stage (zMid pre instruction) := holds.1
  have sizeWord : payload.size < UInt256.size := by
    have huge : 49152 < UInt256.size := by decide
    omega
  have charge := stage_instruction_cost payload stage (zMid pre instruction) dataMid sizeWord
  have memory := stage_memory_cost payload stage pre holds.1 holds.2.1 bounded
  have budget := stage_budget payload.size stage
  have previous := holds.2.2
  have gasMemory : EVM.memoryExpansionCost pre instruction ≤ pre.gasAvailable.toNat := by
    change EVM.memoryExpansionCost pre (stageInstruction stage).1 ≤ _
    rw [memory]
    omega
  have debit := gas_sub_toNat pre.gasAvailable (EVM.memoryExpansionCost pre instruction) gasMemory
  have gasInstruction : EVM.C' (zMid pre instruction) instruction ≤
      (zMid pre instruction).gasAvailable.toNat := by
    change EVM.C' (zMid pre instruction) (stageInstruction stage).1 ≤ _
    rw [charge]
    change stageCost payload.size stage ≤
      (pre.gasAvailable - UInt256.ofNat (EVM.memoryExpansionCost pre instruction)).toNat
    rw [debit]
    change EVM.memoryExpansionCost pre (stageInstruction stage).1 ≤ _ at gasMemory
    change (pre.gasAvailable.toNat - EVM.memoryExpansionCost pre (stageInstruction stage).1) ≥ _
    rw [memory]
    omega
  rw [stage_checks payload stage pre jumps holds.1]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr gasMemory), if_neg (Nat.not_lt.mpr gasInstruction), charge]

/-- Every reachable stage has an actual successful primitive step at positive
fuel; the stack premises are derived from DataAt, not supplied by an oracle. -/
theorem stage_step_success (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (fuel cost : Nat) (holds : DataAt payload stage pre) :
    ∃ post, EVM.step (fuel + 1) cost (some (stageInstruction stage)) pre = .ok post := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, step_PUSH1 fuel cost pre (.ofNat 11)⟩
  · exact ⟨_, step_CODESIZE fuel cost pre⟩
  · have popped : pre.stack.pop2 = some ([], UInt256.ofNat (11 + payload.size), UInt256.ofNat 11) := by
      rw [holds.2.2.1]; rfl
    exact ⟨_, step_SUB fuel cost pre _ _ _ popped⟩
  · exact ⟨_, step_DUP1 fuel cost pre (.ofNat payload.size) [] holds.2.2.1⟩
  · exact ⟨_, step_PUSH1 fuel cost pre (.ofNat 11)⟩
  · exact ⟨_, step_PUSH0 fuel cost pre⟩
  · have popped : pre.stack.pop3 = some ([UInt256.ofNat payload.size], UInt256.ofNat 0,
        UInt256.ofNat 11, UInt256.ofNat payload.size) := by rw [holds.2.2.1]; rfl
    exact ⟨_, step_CODECOPY fuel cost pre _ _ _ _ popped⟩
  · exact ⟨_, step_PUSH0 fuel cost pre⟩
  · have popped : pre.stack.pop2 = some ([], UInt256.ofNat 0, UInt256.ofNat payload.size) := by
      rw [holds.2.2.1]; rfl
    exact ⟨_, step_RETURN fuel cost pre _ _ _ popped⟩

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
