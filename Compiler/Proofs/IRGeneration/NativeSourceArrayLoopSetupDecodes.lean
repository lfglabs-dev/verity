import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLengthFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupDecodes
open EvmYul EVM EVM.Proof

theorem immediate296 : NativeSourceAbiWrite.code.extract' 297 298 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[297]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (297 < 2^64 && 298 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 297 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem immediate298 : NativeSourceAbiWrite.code.extract' 299 300 = ⟨#[4]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[299]? = some 4 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (299 < 2^64 && 300 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 299 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode296 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 296) = some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 296 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 296).toNat = 296 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 297 298), 1)) = _
  rw [immediate296]
  decide

theorem decode298 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 298) = some (.Push .PUSH1, some (UInt256.ofNat 4, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 298 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 298).toNat = 298 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 299 300), 1)) = _
  rw [immediate298]
  decide

theorem decode300 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 300) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 300 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 300).toNat = 300 by decide, byte]
  decide

theorem decode301 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 301) = some (.DUP7, none) := by
  have byte : NativeSourceAbiWrite.code.get? 301 = some 134 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 301).toNat = 301 by decide, byte]
  decide

theorem decode302 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 302) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 302 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 302).toNat = 302 by decide, byte]
  decide

theorem decode303 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 303) = some (.SWAP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 303 = some 147 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 303).toNat = 303 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupDecodes
