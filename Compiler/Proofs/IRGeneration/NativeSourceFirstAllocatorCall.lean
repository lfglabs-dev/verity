import Compiler.Proofs.IRGeneration.NativeSourceSizedFields

namespace Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCall
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode627 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 627) = some (.DUP7, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 627).toNat = some 134 := by
    have index : (UInt256.ofNat 627).toNat = 627 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

theorem immediate : NativeSourceAbiWrite.code.extract' 629 631 = ⟨#[3, 142]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte1 : NativeSourceAbiWrite.code.data[629]? = some 3 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte2 : NativeSourceAbiWrite.code.data[630]? = some 142 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (629 < 2^64 && 631 < 2^64) = true by decide, if_true,
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
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 629 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 630 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte2)

theorem decode628 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 628) =
    some (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 628 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 628).toNat = 628 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 629 631), 2)) = _
  rw [immediate]
  decide

def duplicated (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC (g :: a :: b :: c :: d :: e :: f :: g :: tail)

theorem duplicate (fuel cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (duplicated cost pre a b c d e f g tail) := by
  have decoded : decodeAt pre = (.DUP7, none) := by
    unfold decodeAt
    rw [code, pc, decode627]
    rfl
  rw [decoded]
  change EvmYul.dup 7 (stepPre cost pre) = _
  unfold EvmYul.dup
  rw [show (stepPre cost pre).stack = pre.stack from rfl, stack]
  rfl

def prepared (cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256) :=
  (stepPre cost (duplicated cost pre a b c d e f g tail)).replaceStackAndIncrPC
    (UInt256.ofNat 910 :: g :: a :: b :: c :: d :: e :: f :: g :: tail) 3

theorem push (fuel cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627) :
    EVM.step (fuel + 1) cost (some (decodeAt (duplicated cost pre a b c d e f g tail)))
      (duplicated cost pre a b c d e f g tail) = .ok (prepared cost pre a b c d e f g tail) := by
  have atPC : (duplicated cost pre a b c d e f g tail).pc = UInt256.ofNat 628 := by
    change pre.pc + UInt256.ofNat 1 = _
    rw [pc]; decide
  have decoded : decodeAt (duplicated cost pre a b c d e f g tail) = (.Push .PUSH2, some (UInt256.ofNat 910, 2)) := by
    unfold decodeAt
    change (EVM.decode pre.executionEnv.code (duplicated cost pre a b c d e f g tail).pc).getD _ = _
    rw [code, atPC, decode628]
    rfl
  rw [decoded]
  rfl

theorem execute (fuel cost : Nat) (pre : EVM.State) (a b c d e f g : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 627)
    (stack : pre.stack = a :: b :: c :: d :: e :: f :: g :: tail) :
    run fuel cost 2 pre = .ok (prepared cost pre a b c d e f g tail) := by
  rw [run, duplicate fuel cost pre a b c d e f g tail code pc stack]
  simp only [Bind.bind, Except.bind]
  rw [run, push fuel cost pre a b c d e f g tail code pc]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorCall
