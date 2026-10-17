import Compiler.Proofs.IRGeneration.NativeSourceArrayEndPrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataDecodes
open EvmYul EVM EVM.Proof

theorem immediate315 : NativeSourceAbiWrite.code.extract' 316 318 = ⟨#[0,91]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  apply ByteArray.ext
  simp only [ByteArray.extract', show (316 < 2^64 && 318 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;>
      simp only [Array.getElem_extract] <;>
      apply Option.some.inj <;>
      rw [← Array.getElem?_eq_getElem] <;>
      simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append] <;>
      norm_num

theorem decode312 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 312) = some (.CALLDATASIZE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 312 = some 54 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 312).toNat = 312 by decide, byte]
  decide

theorem decode313 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 313) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 313 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 313).toNat = 313 by decide, byte]
  decide

theorem decode314 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 314) = some (.GT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 314 = some 17 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 314).toNat = 314 by decide, byte]
  decide

theorem decode318 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 318) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 318 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 318).toNat = 318 by decide, byte]
  decide

theorem decode315 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 315) =
    some (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 315 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 315).toNat = 315 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 316 318), 2)) = _
  rw [immediate315]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayCalldataDecodes
