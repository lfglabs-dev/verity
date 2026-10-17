import Compiler.Proofs.IRGeneration.NativeSourceAddressInputReturn
import EvmYul.EVM.Proof.Block

namespace Compiler.Proofs.IRGeneration.NativeSourceEmptyRevert
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode91 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 91) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 91 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 91).toNat = 91 by decide, byte]
  decide

theorem decode92 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 92) = some (.Push .PUSH0, none) := by
  have byte : NativeSourceAbiWrite.code.get? 92 = some 95 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 92).toNat = 92 by decide, byte]
  decide

theorem decode93 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 93) = some (.DUP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 93 = some 128 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 93).toNat = 93 by decide, byte]
  decide

theorem decode94 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 94) = some (.REVERT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 94 = some 253 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 94).toNat = 94 by decide, byte]
  decide

def entered (cost : Nat) (pre : EVM.State) : EVM.State :=
  (stepPre cost pre).incrPC
def pushed (cost : Nat) (pre : EVM.State) : EVM.State :=
  (stepPre cost (entered cost pre)).replaceStackAndIncrPC (UInt256.ofNat 0 :: pre.stack)
def ready (cost : Nat) (pre : EVM.State) : EVM.State :=
  (stepPre cost (pushed cost pre)).replaceStackAndIncrPC (UInt256.ofNat 0 :: UInt256.ofNat 0 :: pre.stack)

theorem transition1 (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (entered cost pre) := by
  have atPC : pre.pc = UInt256.ofNat 91 := by
    exact pc
  have decoded : decodeAt pre = (.JUMPDEST, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code pre.pc).getD _ = _
    rw [code, atPC, decode91]; rfl
  rw [decoded]
  rfl

theorem transition2 (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91) :
    EVM.step (fuel + 1) cost (some (decodeAt (entered cost pre))) (entered cost pre) = .ok (pushed cost pre) := by
  have atPC : (entered cost pre).pc = UInt256.ofNat 92 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (entered cost pre) = (.Push .PUSH0, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (entered cost pre).pc).getD _ = _
    rw [code, atPC, decode92]; rfl
  rw [decoded]
  rfl

theorem transition3 (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) = .ok (ready cost pre) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 93 := by
    change (pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.DUP1, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode93]; rfl
  rw [decoded]
  rfl

theorem execute_ready (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91) :
    run fuel cost 3 pre = .ok (ready cost pre) := by
  rw [run, transition1 fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, transition2 fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, transition3 fuel cost pre code pc]
  rfl

def reverted (cost : Nat) (pre : EVM.State) (tail : Stack UInt256) : EVM.State :=
  let charged := stepPre cost pre
  ({ charged with toMachineState := (charged.toMachineState.evmRevert
      (UInt256.ofNat 0) (UInt256.ofNat 0)) } : EVM.State).replaceStackAndIncrPC tail

theorem revert_step (fuel cost : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail) :
    EVM.step (fuel + 1) cost (some (.REVERT, none)) pre = .ok (reverted cost pre tail) := by
  change EVM.binaryMachineStateOp MachineState.evmRevert (stepPre cost pre) = _
  unfold EVM.binaryMachineStateOp
  simp only [stepPre, stack]
  rfl

theorem output_empty (cost : Nat) (pre : EVM.State) (tail : Stack UInt256) :
    (reverted cost pre tail).H_return = ByteArray.empty := by
  change pre.memory.readWithPadding 0 0 = _
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding]
  rfl

theorem checked_revert (fuel cost : Nat) (jumps : Array UInt256) (pre mid : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 94)
    (stack : pre.stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail)
    (checked : Z jumps .REVERT pre = .ok (mid, cost)) :
    EVM.X (fuel + 2) jumps pre = .ok (.revert (reverted cost mid tail).gasAvailable ByteArray.empty) := by
  have decoded : decodeAt pre = (.REVERT, none) := by
    unfold decodeAt
    rw [code, pc, decode94]; rfl
  have midStack : mid.stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: tail := (Z_ok_stack checked).trans stack
  have step := revert_step fuel cost mid tail midStack
  have halt : H (reverted cost mid tail).toMachineState .REVERT = some ByteArray.empty := by
    change some (reverted cost mid tail).H_return = _
    rw [output_empty]
  exact X_succ_of_revert decoded checked step halt rfl

theorem ready_frame (cost : Nat) (pre : EVM.State) (pc : pre.pc = UInt256.ofNat 91) :
    (ready cost pre).stack = UInt256.ofNat 0 :: UInt256.ofNat 0 :: pre.stack ∧
      (ready cost pre).pc = UInt256.ofNat 94 ∧
      (ready cost pre).executionEnv.code = pre.executionEnv.code ∧
      (ready cost pre).memory = pre.memory := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  change ((pre.pc + UInt256.ofNat 1) + UInt256.ofNat 1) + UInt256.ofNat 1 = _
  rw [pc]; decide

theorem ready_checked_revert (fuel prefixCost revertCost : Nat) (jumps : Array UInt256) (pre mid : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 91)
    (checked : Z jumps .REVERT (ready prefixCost pre) = .ok (mid, revertCost)) :
    EVM.X (fuel + 2) jumps (ready prefixCost pre) =
      .ok (.revert (reverted revertCost mid pre.stack).gasAvailable ByteArray.empty) := by
  have frame := ready_frame prefixCost pre pc
  exact checked_revert fuel revertCost jumps (ready prefixCost pre) mid pre.stack
    (frame.2.2.1.trans code) frame.2.1 frame.1 checked

end Compiler.Proofs.IRGeneration.NativeSourceEmptyRevert
