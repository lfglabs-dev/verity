import Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayMemory

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreDecodes
open EvmYul EVM EVM.Proof

theorem decode292 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 292) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 292 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 292).toNat = 292 by decide, byte]
  decide

theorem decode293 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 293) = some (.DUP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 293 = some 129 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 293).toNat = 293 by decide, byte]
  decide

theorem decode294 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 294) = some (.DUP5, none) := by
  have byte : NativeSourceAbiWrite.code.get? 294 = some 132 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 294).toNat = 294 by decide, byte]
  decide

theorem decode295 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 295) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 295 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 295).toNat = 295 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayLengthStoreDecodes
