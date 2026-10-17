import Compiler.Proofs.IRGeneration.NativeSourceFourthField

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldSizeEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode619 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 619) = some (.SUB, none) := by
  unfold EVM.decode
  have byte : NativeSourceAbiWrite.code.get? (UInt256.ofNat 619).toNat = some 3 := by
    have index : (UInt256.ofNat 619).toNat = 619 := by decide
    rw [index, NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  rw [byte]
  decide

def sized (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :=
  (stepPre cost pre).replaceStackAndIncrPC ((a - b) :: tail)

theorem step (fuel cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 619)
    (stack : pre.stack = a :: b :: tail) :
    EVM.step (fuel + 1) cost (some (decodeAt pre)) pre = .ok (sized cost pre a b tail) := by
  have decoded : decodeAt pre = (.SUB, none) := by
    unfold decodeAt
    rw [code, pc, decode619]
    rfl
  rw [decoded]
  change EVM.execBinOp UInt256.sub (stepPre cost pre) = _
  unfold EVM.execBinOp
  rw [show (stepPre cost pre).stack = pre.stack from rfl, stack]
  rfl

theorem immediate620 : NativeSourceAbiWrite.code.extract' 621 622 = ⟨#[31]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[621]? = some 31 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (621 < 2^64 && 622 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 621 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode620 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 620) =
    some (.Push .PUSH1, some (UInt256.ofNat 31, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 620 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 620).toNat = 620 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 621 622), 1)) = _
  rw [immediate620]
  decide


end Compiler.Proofs.IRGeneration.NativeSourceFieldSizeEntry
