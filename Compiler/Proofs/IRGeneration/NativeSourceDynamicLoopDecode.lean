import Compiler.Proofs.IRGeneration.NativeSourceDynamicElementCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopDecode
open EvmYul

theorem decode741 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 741) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 741 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 741).toNat = 741 by decide, byte]
  decide

theorem decode744 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 744) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 744 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 744).toNat = 744 by decide, byte]
  decide

theorem decode747 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 747) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 747 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 747).toNat = 747 by decide, byte]
  decide

theorem decode751 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 751) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 751 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 751).toNat = 751 by decide, byte]
  decide

theorem decode755 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 755) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 755 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 755).toNat = 755 by decide, byte]
  decide

theorem decode760 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 760) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 760 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 760).toNat = 760 by decide, byte]
  decide

theorem decode765 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 765) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 765 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 765).toNat = 765 by decide, byte]
  decide

theorem decode767 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 767) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 767 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 767).toNat = 767 by decide, byte]
  decide

theorem decode773 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 773) = some (.MSTORE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 773 = some 82 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 773).toNat = 773 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceDynamicLoopDecode
