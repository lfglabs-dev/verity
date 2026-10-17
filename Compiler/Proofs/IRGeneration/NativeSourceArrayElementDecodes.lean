import Compiler.Proofs.IRGeneration.NativeSourceMarketArrayCursor

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementDecodes
open EvmYul EVM EVM.Proof

theorem immediate807 : NativeSourceAbiWrite.code.extract' 808 809 = ⟨#[128]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  have byte : NativeSourceAbiWrite.code.data[808]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (808 < 2^64 && 809 < 2^64) = true by decide, if_true, ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]; decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 808 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode807 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 807) = some (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 807 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 807).toNat = 807 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 808 809), 1)) = _
  rw [immediate807]
  decide

theorem decode806 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 806) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 806 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 806).toNat = 806 by decide, byte]
  decide

theorem decode809 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 809) = some (.DUP4, none) := by
  have byte : NativeSourceAbiWrite.code.get? 809 = some 131 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 809).toNat = 809 by decide, byte]
  decide

theorem decode810 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 810) = some (.CALLDATASIZE, none) := by
  have byte : NativeSourceAbiWrite.code.get? 810 = some 54 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 810).toNat = 810 by decide, byte]
  decide

theorem decode811 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 811) = some (.SUB, none) := by
  have byte : NativeSourceAbiWrite.code.get? 811 = some 3 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 811).toNat = 811 by decide, byte]
  decide

theorem decode812 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 812) = some (.SLT, none) := by
  have byte : NativeSourceAbiWrite.code.get? 812 = some 18 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 812).toNat = 812 by decide, byte]
  decide

theorem decode816 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 816) = some (.JUMPI, none) := by
  have byte : NativeSourceAbiWrite.code.get? 816 = some 87 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 816).toNat = 816 by decide, byte]
  decide

theorem immediate813 : NativeSourceAbiWrite.code.extract' 814 816 = ⟨#[0,91]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]; decide
  apply ByteArray.ext
  simp only [ByteArray.extract', show (814 < 2^64 && 816 < 2^64) = true by decide, if_true, ByteArray.data_extract]
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

theorem decode813 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 813) =
    some (.Push .PUSH2, some (UInt256.ofNat 91, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 813 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 813).toNat = 813 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 814 816), 2)) = _
  rw [immediate813]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementDecodes
