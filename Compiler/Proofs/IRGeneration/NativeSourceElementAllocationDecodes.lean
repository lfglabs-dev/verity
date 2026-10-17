import Compiler.Proofs.IRGeneration.NativeSourceArrayElementOutcome

namespace Compiler.Proofs.IRGeneration.NativeSourceElementAllocationDecodes
open EvmYul EVM EVM.Proof

theorem immediate817 : NativeSourceAbiWrite.code.extract' 818 819 = ⟨#[64]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[818]? = some 64 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (818 < 2^64 && 819 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 818 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode817 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 817) = some (.Push .PUSH1, some (UInt256.ofNat 64, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 817 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 817).toNat = 817 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 818 819), 1)) = _
  rw [immediate817]
  decide

theorem immediate821 : NativeSourceAbiWrite.code.extract' 822 823 = ⟨#[128]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[822]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (822 < 2^64 && 823 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 822 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode821 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 821) = some (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 821 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 821).toNat = 821 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 822 823), 1)) = _
  rw [immediate821]
  decide

theorem decode819 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 819) = some (.MLOAD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 819 = some 81 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 819).toNat = 819 by decide, byte]
  decide

theorem decode820 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 820) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 820 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 820).toNat = 820 by decide, byte]
  decide

theorem decode823 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 823) = some (.DUP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 823 = some 130 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 823).toNat = 823 by decide, byte]
  decide

theorem decode824 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 824) = some (.ADD, none) := by
  have byte : NativeSourceAbiWrite.code.get? 824 = some 1 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 824).toNat = 824 by decide, byte]
  decide

theorem decode825 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 825) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 825 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 825).toNat = 825 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceElementAllocationDecodes
