import Compiler.Proofs.IRGeneration.NativeConstructorLengthWord
import Compiler.Proofs.IRGeneration.NativeConstructorDataInvariant

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames
open Verity.Core.Model.MidnightInitcode

theorem data_push_length (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨0, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.Push .PUSH1, some (UInt256.ofNat 11, 1))) pre = .ok post) :
    DataAt payload ⟨1, by decide⟩ post := by
  have exactStep := step_PUSH1 fuel gasCost pre (.ofNat 11)
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 2).toNat = 2
    have pc : pre.pc.toNat = 0 := holds.2.1
    rw [header_pc_add pre.pc 2 (by omega) (by decide), pc]
  · change _ :: _ = stageStack payload.size ⟨1, by decide⟩
    rw [holds.2.2.1]; rfl
  · intro impossible
    change 7 ≤ (1 : Nat) at impossible
    omega

theorem data_code_size (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨1, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.CODESIZE, none)) pre = .ok post) :
    DataAt payload ⟨2, by decide⟩ post := by
  have exactStep := step_CODESIZE fuel gasCost pre
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 3
    have pc : pre.pc.toNat = 2 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · change _ :: _ = stageStack payload.size ⟨2, by decide⟩
    rw [holds.1, initcode_size, holds.2.2.1]; rfl
  · intro impossible
    change 7 ≤ (2 : Nat) at impossible
    omega

theorem data_duplicate_length (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨3, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.DUP1, none)) pre = .ok post) :
    DataAt payload ⟨4, by decide⟩ post := by
  have exactStep := step_DUP1 fuel gasCost pre (.ofNat payload.size) [] holds.2.2.1
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 5
    have pc : pre.pc.toNat = 4 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · change _ :: _ = stageStack payload.size ⟨4, by decide⟩
    rfl
  · intro impossible
    change 7 ≤ (4 : Nat) at impossible
    omega

theorem data_push_offset (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨4, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.Push .PUSH1, some (UInt256.ofNat 11, 1))) pre = .ok post) :
    DataAt payload ⟨5, by decide⟩ post := by
  have exactStep := step_PUSH1 fuel gasCost pre (.ofNat 11)
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 2).toNat = 7
    have pc : pre.pc.toNat = 5 := holds.2.1
    rw [header_pc_add pre.pc 2 (by omega) (by decide), pc]
  · change _ :: _ = stageStack payload.size ⟨5, by decide⟩
    rw [holds.2.2.1]; rfl
  · intro impossible
    change 7 ≤ (5 : Nat) at impossible
    omega

theorem data_push_destination (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨5, by decide⟩ pre)
    (success : EVM.step (fuel + 1) gasCost (some (.Push .PUSH0, none)) pre = .ok post) :
    DataAt payload ⟨6, by decide⟩ post := by
  have exactStep := step_PUSH0 fuel gasCost pre
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 8
    have pc : pre.pc.toNat = 7 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · change _ :: _ = stageStack payload.size ⟨6, by decide⟩
    rw [holds.2.2.1]; rfl
  · intro impossible
    change 7 ≤ (6 : Nat) at impossible
    omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor

namespace Compiler.Proofs.IRGeneration.NativeMidnightConstructor
open EvmYul EVM.Proof NativeInitcodeFrames

theorem data_subtract_header (payload : ByteArray) (pre post : EVM.State)
    (fuel gasCost : Nat) (holds : DataAt payload ⟨2, by decide⟩ pre)
    (bounded : 11 + payload.size < UInt256.size)
    (success : EVM.step (fuel + 1) gasCost (some (.SUB, none)) pre = .ok post) :
    DataAt payload ⟨3, by decide⟩ post := by
  have popped : pre.stack.pop2 = some ([], UInt256.ofNat (11 + payload.size),
      UInt256.ofNat 11) := by rw [holds.2.2.1]; rfl
  have exactStep := step_SUB fuel gasCost pre [] (.ofNat (11 + payload.size))
    (.ofNat 11) popped
  have same := Except.ok.inj (exactStep.symm.trans success)
  subst post
  refine ⟨holds.1, ?_, ?_, ?_⟩
  · change (pre.pc + UInt256.ofNat 1).toNat = 4
    have pc : pre.pc.toNat = 3 := holds.2.1
    rw [header_pc_add pre.pc 1 (by omega) (by decide), pc]
  · change [UInt256.ofNat (11 + payload.size) - UInt256.ofNat 11] = [UInt256.ofNat payload.size]
    rw [subtract_header_length payload.size bounded]
  · intro impossible
    change 7 ≤ (3 : Nat) at impossible
    omega

end Compiler.Proofs.IRGeneration.NativeMidnightConstructor
