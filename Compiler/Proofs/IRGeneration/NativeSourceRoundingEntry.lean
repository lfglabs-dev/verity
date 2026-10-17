import Compiler.Proofs.IRGeneration.NativeSourceSizedPacking

namespace Compiler.Proofs.IRGeneration.NativeSourceRoundingEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate : NativeSourceAbiWrite.code.extract' 670 671 = ⟨#[31]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[670]? = some 31 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (670 < 2^64 && 671 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 670 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)


theorem byte669 : NativeSourceAbiWrite.code.get? 669 = some 96 := by
  rw [NativeSourcePackingCopy.get_data]
  simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
  norm_num

theorem decode669 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 669) =
    some (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
  unfold EVM.decode
  rw [show (UInt256.ofNat 669).toNat = 669 by decide, byte669]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 670 671), 1)) = _
  rw [immediate]
  decide

theorem decode671 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 671) = some (.NOT, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 671).toNat = some 25 := by
    have index : (UInt256.ofNat 671).toNat = 671 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def pushed (cost : Nat) (pre : EVM.State) :=
  (stepPre cost pre).replaceStackAndIncrPC (UInt256.ofNat 31 :: pre.stack) 2

def masked (cost : Nat) (pre : EVM.State) :=
  (stepPre cost (pushed cost pre)).replaceStackAndIncrPC (UInt256.lnot (UInt256.ofNat 31) :: pre.stack)

theorem push (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 669) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (pushed cost pre) := by
  have decoded : decodeAt pre = (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
    unfold decodeAt
    rw [code, pc, decode669]
    rfl
  rw [decoded]
  exact NativeMidnightConstructor.step_PUSH1 fuel cost pre (UInt256.ofNat 31)

theorem invert (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 669) :
    EVM.step (fuel + 1) cost (some (decodeAt (pushed cost pre))) (pushed cost pre) = .ok (masked cost pre) := by
  have atPC : (pushed cost pre).pc = UInt256.ofNat 671 := by
    change pre.pc + UInt256.ofNat 2 = _
    rw [pc]; decide
  have decoded : decodeAt (pushed cost pre) = (.NOT, none) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (pushed cost pre).pc).getD _ = _
    rw [code, atPC, decode671]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 669) :
    run fuel cost 2 pre = .ok (masked cost pre) := by
  rw [run, push fuel cost pre code pc]
  simp only [Bind.bind, Except.bind]
  rw [run, invert fuel cost pre code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceRoundingEntry
