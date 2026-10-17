import Compiler.Proofs.IRGeneration.NativeConstructorHeaderTransitions
import Compiler.Proofs.IRGeneration.NativeHeaderExactDecode

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

def stageInstruction : Fin 9 → Instruction
  | ⟨0, _⟩ => (.Push .PUSH1, some (UInt256.ofNat 11, 1))
  | ⟨1, _⟩ => (.CODESIZE, none)
  | ⟨2, _⟩ => (.SUB, none)
  | ⟨3, _⟩ => (.DUP1, none)
  | ⟨4, _⟩ => (.Push .PUSH1, some (UInt256.ofNat 11, 1))
  | ⟨5, _⟩ => (.Push .PUSH0, none)
  | ⟨6, _⟩ => (.CODECOPY, none)
  | ⟨7, _⟩ => (.Push .PUSH0, none)
  | ⟨8, _⟩ => (.RETURN, none)

theorem data_decode (payload : ByteArray) (stage : Fin 9) (pre : EVM.State)
    (holds : DataAt payload stage pre) : decodeAt pre = stageInstruction stage := by
  have inside : pre.pc.toNat < 11 := by
    rw [holds.2.1]
    obtain ⟨n, small⟩ := stage
    have positions : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨
        n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [stagePC] <;> omega
  unfold decodeAt
  rw [holds.1, decode_exact_header payload pre.pc inside]
  obtain ⟨n, small⟩ := stage
  have positions : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨
      n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have pc := holds.2.1
  all_goals simp only [stagePC] at pc
  all_goals simp only [EVM.decode, pc]
  all_goals rfl

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames

private theorem data_continuation {payload : ByteArray} {post : EVM.State}
    {instruction : Instruction} (holds : DataInvariant payload post)
    (nonhalting : H post.toMachineState instruction.1 = none) :
    (H post.toMachineState instruction.1 = none → DataInvariant payload post) ∧
    (∀ bytes, H post.toMachineState instruction.1 = some bytes →
      instruction.1 ≠ .REVERT → bytes = payload) := by
  refine ⟨fun _ => holds, ?_⟩
  intro bytes halted _notRevert
  rw [nonhalting] at halted
  cases halted

theorem data_step_output (payload : ByteArray) (bounded : payload.size < 2^64)
    (fuel gasCost : Nat) (instruction : Instruction) (pre post : EVM.State)
    (holds : DataInvariant payload pre) (decoded : instruction = decodeAt pre)
    (success : EVM.step fuel gasCost (some instruction) pre = .ok post) :
    (H post.toMachineState instruction.1 = none → DataInvariant payload post) ∧
    (∀ bytes, H post.toMachineState instruction.1 = some bytes →
      instruction.1 ≠ .REVERT → bytes = payload) := by
  have noWrap : 11 + payload.size < UInt256.size := by
    have huge : 2^64 + 11 < UInt256.size := by decide
    omega
  subst instruction
  cases fuel with
  | zero => change Except.error EVM.ExecutionException.OutOfFuel = Except.ok post at success; cases success
  | succ fuel =>
    obtain ⟨⟨stage, small⟩, holds⟩ := holds
    rw [data_decode payload ⟨stage, small⟩ pre holds] at success ⊢
    have positions : stage = 0 ∨ stage = 1 ∨ stage = 2 ∨ stage = 3 ∨ stage = 4 ∨
        stage = 5 ∨ stage = 6 ∨ stage = 7 ∨ stage = 8 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact data_continuation ⟨⟨1, by decide⟩, data_push_length payload pre post fuel gasCost holds success⟩ rfl
    · exact data_continuation ⟨⟨2, by decide⟩, data_code_size payload pre post fuel gasCost holds success⟩ rfl
    · exact data_continuation ⟨⟨3, by decide⟩, data_subtract_header payload pre post fuel gasCost holds noWrap success⟩ rfl
    · exact data_continuation ⟨⟨4, by decide⟩, data_duplicate_length payload pre post fuel gasCost holds success⟩ rfl
    · exact data_continuation ⟨⟨5, by decide⟩, data_push_offset payload pre post fuel gasCost holds success⟩ rfl
    · exact data_continuation ⟨⟨6, by decide⟩, data_push_destination payload pre post fuel gasCost holds success⟩ rfl
    · exact data_continuation ⟨⟨7, by decide⟩, data_copy_step payload pre post fuel gasCost holds bounded success⟩ rfl
    · exact data_continuation ⟨⟨8, by decide⟩, data_return_setup payload pre post fuel gasCost holds success⟩ rfl
    · have sizeBound : payload.size < UInt256.size := by
        have huge : 2^64 < UInt256.size := by decide
        omega
      have returned := data_return_payload payload pre post fuel gasCost holds sizeBound success
      refine ⟨?_, ?_⟩
      · intro continues
        change H post.toMachineState .RETURN = none at continues
        rw [returned] at continues
        cases continues
      · intro bytes halted _notRevert
        change H post.toMachineState .RETURN = some bytes at halted
        exact Option.some.inj (halted.symm.trans returned)

/-- Every successful actual native constructor execution returns its appended
payload, derived from all real steps rather than assumed at the RETURN state. -/
theorem success_output (payload : ByteArray) (bounded : payload.size < 2^64)
    (jumps : Array UInt256) (pre post : EVM.State) (fuel : Nat) (output : ByteArray)
    (code : pre.executionEnv.code = Verity.Core.Model.MidnightInitcode.initcode payload)
    (pc : pre.pc.toNat = 0) (stack : pre.stack = [])
    (success : EVM.X fuel jumps pre = .ok (.success post output)) : output = payload := by
  exact X_output_of_invariant (DataInvariant payload) payload
    (dataInvariant_charge payload) (data_step_output payload bounded)
    fuel jumps pre post output (data_initial payload pre code pc stack) success

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
