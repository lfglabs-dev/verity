import Compiler.Proofs.IRGeneration.NativeSourceDynamicIncrements

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicBackedge
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate782 : NativeSourceAbiWrite.code.extract' 783 785 = ⟨#[2, 39]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[783]? = some 2 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[784]? = some 39 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (783 < 2^64 && 785 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 783 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 784 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode782 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 782) = some (.Push .PUSH2, some (UInt256.ofNat 551, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 782 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 782).toNat = 782 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 783 785), 2)) = _
  rw [immediate782]
  decide

theorem decode785 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 785) = some (.JUMP, none) := by
  have byte : NativeSourceAbiWrite.code.get? 785 = some 86 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 785).toNat = 785 by decide, byte]
  decide

theorem decode551 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 551) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 551 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 551).toNat = 551 by decide, byte]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 551 :: pre.stack) 3

def returned (cost : Nat) (pre : EVM.State) : EVM.State :=
  { stepPre cost (pushed cost pre) with pc := UInt256.ofNat 551, stack := pre.stack }

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 782) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH2, some (UInt256.ofNat 551, 2)) := by
    unfold decodeAt
    rw [code, pc, decode782]; rfl
  rw [decoded]
  rfl

theorem jump (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 782) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) = .ok (returned cost pre) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 785 := by
    change pre.pc + UInt256.ofNat 3 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.JUMP, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode785]; rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 782) :
    run fuel cost 2 pre = .ok (returned cost pre) := by
  rw [run, push fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, jump fuel cost pre code pc]
  rfl

theorem memory (cost : Nat) (pre : EVM.State) : (returned cost pre).memory = pre.memory := by
  rfl

theorem header_pc (cost : Nat) (pre : EVM.State) : (returned cost pre).pc = UInt256.ofNat 551 := by
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceDynamicBackedge
