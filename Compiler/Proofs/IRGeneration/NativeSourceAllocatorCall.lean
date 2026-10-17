import Compiler.Proofs.IRGeneration.NativeSourceRoundedPacking

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorCall
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode676 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 676) = some (.DUP3, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 676).toNat = some 130 := by
    have index : (UInt256.ofNat 676).toNat = 676 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem immediate : NativeSourceAbiWrite.code.extract' 678 680 = ⟨#[3, 142]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[678]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[679]? = some 142 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (678 < 2^64 && 680 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract, Nat.add_zero]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 678 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 679 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode677 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 677) =
    some (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 677 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 677).toNat = 677 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 678 680), 2)) = _
  rw [immediate]
  decide

def duplicated (cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (c :: a :: b :: c :: tail)

theorem duplicate (fuel cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 676)
    (stack : pre.stack = a :: b :: c :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (duplicated cost pre a b c tail) := by
  have decoded : decodeAt pre = (.DUP3, none) := by
    unfold decodeAt
    rw [code, pc, decode676]
    rfl
  rw [decoded]
  change EvmYul.dup 3 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, stack]
  rfl

def prepared (cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (duplicated cost pre a b c tail)).replaceStackAndIncrPC
    (UInt256.ofNat 910 :: c :: a :: b :: c :: tail) 3

theorem push (fuel cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 676) :
    EVM.step (fuel + 1) cost (some (decodeAt (duplicated cost pre a b c tail)))
      (duplicated cost pre a b c tail) = .ok (prepared cost pre a b c tail) := by
  have atPC : (duplicated cost pre a b c tail).pc = UInt256.ofNat 677 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (duplicated cost pre a b c tail) = (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (duplicated cost pre a b c tail).pc).getD _ = _
    rw [code, atPC, decode677]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 676)
    (stack : pre.stack = a :: b :: c :: tail) :
    run fuel cost 2 pre = .ok (prepared cost pre a b c tail) := by
  rw [run, duplicate fuel cost pre a b c tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, push fuel cost pre a b c tail code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorCall
