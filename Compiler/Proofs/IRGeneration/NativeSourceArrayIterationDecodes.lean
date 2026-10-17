import Compiler.Proofs.IRGeneration.NativeSourceMarketArrayBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayIterationDecodes
open EvmYul EVM EVM.Proof

theorem immediate327 : NativeSourceAbiWrite.code.extract' 328 330 = ⟨#[3,38]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  apply ByteArray.ext
  simp only [ByteArray.extract', show (328 < 2^64 && 330 < 2^64) = true by decide, if_true, ByteArray.data_extract]
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

theorem decode324 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 324) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 324 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 324).toNat = 324 by decide, byte]
  decide

theorem decode325 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 325) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 325 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 325).toNat = 325 by decide, byte]
  decide

theorem decode326 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 326) = some (.LT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 326 = some 16 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 326).toNat = 326 by decide, byte]
  decide

theorem decode330 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 330) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 330 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 330).toNat = 330 by decide, byte]
  decide

theorem decode327 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 327) =
    some (.Push .PUSH2, some (UInt256.ofNat 806, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 327 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 327).toNat = 327 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 328 330), 2)) = _
  rw [immediate327]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayIterationDecodes
