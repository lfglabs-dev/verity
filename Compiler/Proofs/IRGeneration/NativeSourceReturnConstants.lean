import Compiler.Proofs.IRGeneration.NativeSourceZeroShuffles

namespace Compiler.Proofs.IRGeneration.NativeSourceReturnConstants
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem immediate579 : NativeSourceAbiWrite.code.extract' 580 581 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[580]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (580 < 2^64 && 581 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 580 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)

theorem decode579 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 579) =
    some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 579 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 579).toNat = 579 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 580 581), 1)) = _
  rw [immediate579]
  decide

theorem immediate582 : NativeSourceAbiWrite.code.extract' 583 585 = ⟨#[2, 169]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[583]? = some 2 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[584]? = some 169 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (583 < 2^64 && 585 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 583 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 584 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode582 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 582) =
    some (.Push .PUSH2, some (UInt256.ofNat 681, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 582 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 582).toNat = 582 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 583 585), 2)) = _
  rw [immediate582]
  decide

theorem immediate587 : NativeSourceAbiWrite.code.extract' 588 590 = ⟨#[2, 120]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte0 : NativeSourceAbiWrite.code.data[588]? = some 2 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  have byte1 : NativeSourceAbiWrite.code.data[589]? = some 120 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (588 < 2^64 && 590 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have bound : index < 2 := by simpa using right
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with zero | one
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 588 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte0)
    · subst index
      simp only [Array.getElem_extract]
      exact Option.some.inj ((Array.getElem?_eq_getElem (by change 589 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte1)

theorem decode587 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 587) =
    some (.Push .PUSH2, some (UInt256.ofNat 632, 2)) := by
  have byte : NativeSourceAbiWrite.code.get? 587 = some 97 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 587).toNat = 587 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH2, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 588 590), 2)) = _
  rw [immediate587]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceReturnConstants
