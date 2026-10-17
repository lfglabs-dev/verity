import Compiler.Proofs.IRGeneration.NativeSourceSecondField

namespace Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldLoad
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode603 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 603) = some (.MLOAD, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 603).toNat = some 81 := by
    have index : (UInt256.ofNat 603).toNat = 603 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem step (fuel cost : Nat) (pre : EVM.State) (address : UInt256) (rest : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 603)
    (stack : pre.stack = address :: rest) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre =
      .ok (NativeSourceLoadStep.loaded cost pre address rest) := by
  have decoded : decodeAt pre = (.MLOAD, none) := by
    unfold decodeAt
    rw [code, pc, decode603]
    rfl
  rw [decoded]
  exact NativeSourceLoadStep.step fuel cost pre address rest stack


theorem decode604 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 604) = some (.AND, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 604).toNat = some 22 := by
    have index : (UInt256.ofNat 604).toNat = 604 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def masked (cost : Nat) (pre : EVM.State) (address mask : UInt256) (tail : Stack UInt256) :=
  let read := NativeSourceLoadStep.loaded cost pre address (mask :: tail)
  (stepPre cost read).replaceStackAndIncrPC ((pre.toMachineState.lookupMemory address).land mask :: tail)

theorem mask_step (fuel cost : Nat) (pre : EVM.State) (address mask : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 603) :
    EVM.step (fuel + 1) cost
      (some (decodeAt (NativeSourceLoadStep.loaded cost pre address (mask :: tail))))
      (NativeSourceLoadStep.loaded cost pre address (mask :: tail)) = .ok (masked cost pre address mask tail) := by
  have atPC : (NativeSourceLoadStep.loaded cost pre address (mask :: tail)).pc = UInt256.ofNat 604 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (NativeSourceLoadStep.loaded cost pre address (mask :: tail)) = (.AND, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code _).getD _ = _
    rw [code, atPC, decode604]
    rfl
  rw [decoded]
  change EVM.execBinOp UInt256.land (stepPre cost (NativeSourceLoadStep.loaded cost pre address (mask :: tail))) = _
  unfold EVM.execBinOp
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (address mask : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 603)
    (stack : pre.stack = address :: mask :: tail) :
    run fuel cost 2 pre = .ok (masked cost pre address mask tail) := by
  rw [run, step fuel cost pre address (mask :: tail) code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, mask_step fuel cost pre address mask tail code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceMaskedFieldLoad
