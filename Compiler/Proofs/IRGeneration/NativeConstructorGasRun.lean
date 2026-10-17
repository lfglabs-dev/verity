import Compiler.Proofs.IRGeneration.NativeConstructorGasStep
import Compiler.Proofs.IRGeneration.NativeConstructorGasAccounting
import Compiler.Proofs.IRGeneration.NativeInitcodeResultRule

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof

theorem stage_nonhalting (stage : Fin 8) (state : EVM.State) :
    H state.toMachineState (stageInstruction ⟨stage.val, by omega⟩).1 = none := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem data_next (payload : ByteArray) (stage : Fin 8) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨stage.val, by omega⟩ pre)
    (bounded : payload.size < 2^64)
    (success : EVM.step (fuel + 1) gasCost
      (some (stageInstruction ⟨stage.val, by omega⟩)) pre = .ok post) :
    DataAt payload ⟨stage.val + 1, by omega⟩ post := by
  obtain ⟨stage, small⟩ := stage
  have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
      stage = 5 ∨ stage = 6 ∨ stage = 7 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact data_push_length payload pre post fuel gasCost holds success
  · exact data_code_size payload pre post fuel gasCost holds success
  · apply data_subtract_header payload pre post fuel gasCost holds ?_ success
    have huge : 2^64 + 11 < UInt256.size := by decide
    omega
  · exact data_duplicate_length payload pre post fuel gasCost holds success
  · exact data_push_offset payload pre post fuel gasCost holds success
  · exact data_push_destination payload pre post fuel gasCost holds success
  · exact data_copy_step payload pre post fuel gasCost holds bounded success
  · exact data_return_setup payload pre post fuel gasCost holds success

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

def GasAt (initial : Nat) (payload : ByteArray) (stage : Fin 9) (state : EVM.State) : Prop :=
  DataAt payload stage state ∧
    state.activeWords = UInt256.ofNat (stageWords payload.size stage) ∧
    state.gasAvailable.toNat + stageSpent payload.size stage = initial

def GasInvariant (initial : Nat) (payload : ByteArray) (state : EVM.State) : Prop :=
  ∃ stage, GasAt initial payload stage state

private theorem gasAt_checked (initial : Nat) (payload : ByteArray) (stage : Fin 9)
    (jumps : Array UInt256) (pre mid : EVM.State) (cost : Nat)
    (holds : GasAt initial payload stage pre) (bounded : payload.size ≤ 49152)
    (checked : Z jumps (stageInstruction stage).1 pre = .ok (mid, cost)) :
    DataAt payload stage mid ∧
      mid.activeWords = UInt256.ofNat (stageWords payload.size stage) ∧
      cost = stageCost payload.size stage ∧ cost ≤ mid.gasAvailable.toNat ∧
      mid.gasAvailable.toNat + (if stage.val = 6 then memoryCost (words payload.size) else 0) =
        pre.gasAvailable.toNat := by
  have frame := Z_ok_state checked
  have dataMid : DataAt payload stage mid := by rw [frame]; exact holds.1
  have costs := checked_gas jumps (stageInstruction stage).1 pre mid cost checked
  have wordBound : payload.size < UInt256.size := by
    have huge : 49152 < UInt256.size := by decide
    omega
  refine ⟨dataMid, ?_, ?_, costs.2.2, ?_⟩
  · rw [frame]; exact holds.2.1
  · exact costs.2.1.trans (stage_instruction_cost payload stage mid dataMid wordBound)
  · rw [stage_memory_cost payload stage pre holds.1 holds.2.1 bounded] at costs
    exact costs.1

theorem gas_next (initial : Nat) (payload : ByteArray) (stage : Fin 8)
    (jumps : Array UInt256) (pre mid post : EVM.State) (fuel cost : Nat)
    (holds : GasAt initial payload ⟨stage.val, by omega⟩ pre)
    (bounded : payload.size ≤ 49152)
    (checked : Z jumps (stageInstruction ⟨stage.val, by omega⟩).1 pre = .ok (mid, cost))
    (success : EVM.step (fuel + 1) cost (some (stageInstruction ⟨stage.val, by omega⟩)) mid = .ok post) :
    GasAt initial payload ⟨stage.val + 1, by omega⟩ post := by
  have facts := gasAt_checked initial payload ⟨stage.val, by omega⟩ jumps pre mid cost holds bounded checked
  have size64 : payload.size < 2^64 := by omega
  have sizeWord : payload.size < UInt256.size := by
    have huge : 49152 < UInt256.size := by decide
    omega
  have machine := data_next_gas_extent payload stage mid post fuel cost facts.1 facts.2.1 sizeWord success
  refine ⟨data_next payload stage mid post fuel cost facts.1 size64 success, machine.2, ?_⟩
  rw [machine.1, gas_sub_toNat _ _ facts.2.2.2.1, stage_spent_next]
  have previous := holds.2.2
  have debit := facts.2.2.2.2
  have instruction := facts.2.2.1
  dsimp only at debit previous instruction ⊢
  omega

theorem gas_return (initial : Nat) (payload : ByteArray)
    (jumps : Array UInt256) (pre mid post : EVM.State) (fuel cost : Nat)
    (holds : GasAt initial payload ⟨8, by decide⟩ pre)
    (bounded : payload.size ≤ 49152)
    (checked : Z jumps .RETURN pre = .ok (mid, cost))
    (success : EVM.step (fuel + 1) cost (some (.RETURN, none)) mid = .ok post) :
    post.gasAvailable.toNat + prefixCost payload.size = initial ∧
      H post.toMachineState .RETURN = some payload := by
  have facts := gasAt_checked initial payload ⟨8, by decide⟩ jumps pre mid cost holds bounded checked
  have zero : cost = 0 := facts.2.2.1
  have gasEq := data_return_gas payload mid post fuel cost facts.1 success
  have sizeWord : payload.size < UInt256.size := by
    have huge : 49152 < UInt256.size := by decide
    omega
  refine ⟨?_, data_return_payload payload mid post fuel cost facts.1 sizeWord success⟩
  rw [gasEq, gas_sub_toNat _ _ facts.2.2.2.1, zero, Nat.sub_zero]
  have debit := facts.2.2.2.2
  have previous : pre.gasAvailable.toNat + prefixCost payload.size = initial := holds.2.2
  change mid.gasAvailable.toNat + 0 = pre.gasAvailable.toNat at debit
  omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

private theorem gas_step_result (initial : Nat) (payload : ByteArray)
    (bounded : payload.size ≤ 49152) (jumps : Array UInt256)
    (fuel cost : Nat) (instruction : Instruction) (pre mid post : EVM.State)
    (holds : GasInvariant initial payload pre) (decoded : instruction = decodeAt pre)
    (checked : Z jumps instruction.1 pre = .ok (mid, cost))
    (success : EVM.step fuel cost (some instruction) mid = .ok post) :
    (H post.toMachineState instruction.1 = none → GasInvariant initial payload post) ∧
    (∀ bytes, H post.toMachineState instruction.1 = some bytes →
      instruction.1 ≠ .REVERT → post.gasAvailable.toNat + prefixCost payload.size = initial) := by
  subst instruction
  cases fuel with
  | zero => change Except.error EVM.ExecutionException.OutOfFuel = Except.ok post at success; cases success
  | succ fuel =>
    obtain ⟨stage, holds⟩ := holds
    rw [data_decode payload stage pre holds.1] at checked success ⊢
    by_cases continuing : stage.val < 8
    · let short : Fin 8 := ⟨stage.val, continuing⟩
      have next := gas_next initial payload short jumps pre mid post fuel cost holds bounded checked success
      refine ⟨fun _ => ⟨_, next⟩, ?_⟩
      intro bytes halted _notRevert
      rw [stage_nonhalting short post] at halted
      cases halted
    · have last : stage = ⟨8, by decide⟩ := by
        apply Fin.ext
        change stage.val = 8
        omega
      subst stage
      have facts := gas_return initial payload jumps pre mid post fuel cost holds bounded checked success
      refine ⟨?_, fun _ _ _ => facts.1⟩
      intro continues
      change H post.toMachineState .RETURN = none at continues
      rw [facts.2] at continues
      cases continues

/-- A successful actual native constructor consumes precisely the canonical
prefix cost. Nat equality rules out any modular underflow in this accounting. -/
theorem success_gas (payload : ByteArray) (bounded : payload.size ≤ 49152)
    (jumps : Array UInt256) (pre post : EVM.State) (fuel : Nat) (output : ByteArray)
    (code : pre.executionEnv.code = initcode payload) (pc : pre.pc.toNat = 0)
    (stack : pre.stack = []) (fresh : pre.activeWords = UInt256.ofNat 0)
    (success : EVM.X fuel jumps pre = .ok (.success post output)) :
    post.gasAvailable.toNat + prefixCost payload.size = pre.gasAvailable.toNat := by
  have data : DataAt payload ⟨0, by decide⟩ pre := by
    refine ⟨code, pc, stack, ?_⟩
    intro impossible
    change 7 ≤ (0 : Nat) at impossible
    omega
  have initial : GasInvariant pre.gasAvailable.toNat payload pre :=
    ⟨⟨0, by decide⟩, data, fresh, by change pre.gasAvailable.toNat + 0 = pre.gasAvailable.toNat; omega⟩
  exact X_result_of_checked_invariant (GasInvariant pre.gasAvailable.toNat payload)
    (fun state _ => state.gasAvailable.toNat + prefixCost payload.size = pre.gasAvailable.toNat)
    jumps (gas_step_result pre.gasAvailable.toNat payload bounded jumps)
    fuel pre post output initial success

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
