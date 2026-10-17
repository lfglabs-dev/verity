import Compiler.Proofs.IRGeneration.NativeSourceDynamicIterationSuffix

namespace Compiler.Proofs.IRGeneration.NativeSourceDynamicEntry
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem decode718 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 718) = some (.JUMPDEST, none) := by
  have byte : NativeSourceAbiWrite.code.get? 718 = some 91 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 718).toNat = 718 by decide, byte]
  decide

theorem decode719 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 719) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 719 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 719).toNat = 719 by decide, byte]
  decide

theorem decode720 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 720) = some (.SWAP2, none) := by
  have byte : NativeSourceAbiWrite.code.get? 720 = some 145 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 720).toNat = 720 by decide, byte]
  decide

theorem decode721 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 721) = some (.SWAP11, none) := by
  have byte : NativeSourceAbiWrite.code.get? 721 = some 154 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 721).toNat = 721 by decide, byte]
  decide

theorem immediate722 : NativeSourceAbiWrite.code.extract' 723 724 = ⟨#[32]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[723]? = some 32 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (723 < 2^64 && 724 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 723 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode722 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 722) = some (.Push .PUSH1, some (UInt256.ofNat 32, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 722 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 722).toNat = 722 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 723 724), 1)) = _
  rw [immediate722]
  decide

theorem immediate724 : NativeSourceAbiWrite.code.extract' 725 726 = ⟨#[128]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[725]? = some 128 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (725 < 2^64 && 726 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 725 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode724 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 724) = some (.Push .PUSH1, some (UInt256.ofNat 128, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 724 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 724).toNat = 724 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 725 726), 1)) = _
  rw [immediate724]
  decide

theorem immediate726 : NativeSourceAbiWrite.code.extract' 727 728 = ⟨#[1]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[727]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (727 < 2^64 && 728 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 727 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode726 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 726) = some (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 726 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 726).toNat = 726 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 727 728), 1)) = _
  rw [immediate726]
  decide

theorem decode728 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 728) = some (.SWAP3, none) := by
  have byte : NativeSourceAbiWrite.code.get? 728 = some 146 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 728).toNat = 728 by decide, byte]
  decide

theorem immediate729 : NativeSourceAbiWrite.code.extract' 730 731 = ⟨#[1]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[730]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (730 < 2^64 && 731 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 730 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode729 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 729) = some (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 729 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 729).toNat = 729 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 730 731), 1)) = _
  rw [immediate729]
  decide

theorem immediate731 : NativeSourceAbiWrite.code.extract' 732 733 = ⟨#[1]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[732]? = some 1 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (732 < 2^64 && 733 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 732 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode731 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 731) = some (.Push .PUSH1, some (UInt256.ofNat 1, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 731 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 731).toNat = 731 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 732 733), 1)) = _
  rw [immediate731]
  decide

theorem immediate733 : NativeSourceAbiWrite.code.extract' 734 735 = ⟨#[160]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[734]? = some 160 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (734 < 2^64 && 735 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 734 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode733 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 733) = some (.Push .PUSH1, some (UInt256.ofNat 160, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 733 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 733).toNat = 733 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 734 735), 1)) = _
  rw [immediate733]
  decide

theorem decode735 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 735) = some (.SHL, none) := by
  have byte : NativeSourceAbiWrite.code.get? 735 = some 27 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 735).toNat = 735 by decide, byte]
  decide

theorem decode736 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 736) = some (.SUB, none) := by
  have byte : NativeSourceAbiWrite.code.get? 736 = some 3 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 736).toNat = 736 by decide, byte]
  decide

theorem decode737 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 737) = some (.DUP16, none) := by
  have byte : NativeSourceAbiWrite.code.get? 737 = some 143 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 737).toNat = 737 by decide, byte]
  decide

theorem immediate738 : NativeSourceAbiWrite.code.extract' 739 740 = ⟨#[96]⟩ := by
  have size : NativeSourceAbiWrite.code.size = 977 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.size_append]
    decide
  have byte : NativeSourceAbiWrite.code.data[739]? = some 96 := by
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  apply ByteArray.ext
  simp only [ByteArray.extract', show (739 < 2^64 && 740 < 2^64) = true by decide, if_true,
    ByteArray.data_extract]
  apply Array.ext
  · simp only [Array.size_extract, size, ByteArray.size_data]
    decide
  · intro index left right
    have zero : index = 0 := by simpa using right
    subst index
    simp only [Array.getElem_extract, Nat.add_zero]
    exact Option.some.inj ((Array.getElem?_eq_getElem (by change 739 < NativeSourceAbiWrite.code.size; rw [size]; omega)).symm.trans byte)

theorem decode738 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 738) = some (.Push .PUSH1, some (UInt256.ofNat 96, 1)) := by
  have byte : NativeSourceAbiWrite.code.get? 738 = some 96 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 738).toNat = 738 by decide, byte]
  change some (Operation.Push Operation.POp.PUSH1, some (uInt256OfByteArray (NativeSourceAbiWrite.code.extract' 739 740), 1)) = _
  rw [immediate738]
  decide

theorem decode740 : EVM.decode NativeSourceAbiWrite.code (UInt256.ofNat 740) = some (.SWAP1, none) := by
  have byte : NativeSourceAbiWrite.code.get? 740 = some 144 := by
    rw [NativeSourcePackingCopy.get_data]
    simp only [NativeSourceAbiWrite.code, ByteArray.data_append, Array.getElem?_append, Array.size_append]
    norm_num
  unfold EVM.decode
  rw [show (UInt256.ofNat 740).toNat = 740 by decide, byte]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceDynamicEntry
