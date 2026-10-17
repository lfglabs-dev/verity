import Compiler.Proofs.IRGeneration.NativeSourceArrayLoopSetupPrefix

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayEndDecodes
open EvmYul EVM EVM.Proof

theorem immediate304 : NativeSourceAbiWrite.code.extract' 305 306 = ⟨#[7]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[305]? = some 7 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (305 < 2^64 && 306 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 305 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode304 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 304) = some (.Push .PUSH1, some (UInt256.ofNat 7, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 304 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 304).toNat = 304 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 305 306), 1)) = _
  rw [immediate304]
  decide

theorem decode306 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 306) = some (.SHL, none) := by
  have byte : NativeSourceAbiWrite.code.get? 306 = some 27 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 306).toNat = 306 by decide, byte]
  decide

theorem decode307 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 307) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 307 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 307).toNat = 307 by decide, byte]
  decide

theorem decode308 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 308) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 308 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 308).toNat = 308 by decide, byte]
  decide

theorem decode309 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 309) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 309 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 309).toNat = 309 by decide, byte]
  decide

theorem decode310 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 310) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 310 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 310).toNat = 310 by decide, byte]
  decide

theorem decode311 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 311) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 311 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 311).toNat = 311 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayEndDecodes
