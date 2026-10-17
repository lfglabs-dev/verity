import Compiler.Proofs.IRGeneration.NativeSourceContextSourceExtract

namespace Compiler.Proofs.IRGeneration.NativeSourceContextFieldSourceExtract
open EvmYul

theorem word_extract (machine : MachineState) (address value : UInt256) (start length : Nat)
    (bounded : length < 2 ^ 64) (above : address.toNat + 32 ≤ start)
    (inside : start + length ≤ machine.memory.size) :
    (machine.mstore address value).memory.extract start (start + length) =
      machine.memory.extract start (start + length) := by
  by_cases zero : length = 0
  · subst length
    rw [NativeSourceEmptyPayload.extract_zero, NativeSourceEmptyPayload.extract_zero]
  · have positive : 0 < length := by omega
    have fits : address.toNat + 32 ≤ machine.memory.size := by omega
    have size := MachineState.size_memory_mstore machine address value fits
    have afterInside : start + length ≤ (machine.mstore address value).memory.size := by rw [size]; exact inside
    exact (ByteArray.readWithPadding_eq_extract _ _ _ positive bounded afterInside).symm.trans
      ((NativeSourceMemoryFrame.read_above machine address value start length fits positive bounded above inside).trans
        (ByteArray.readWithPadding_eq_extract _ _ _ positive bounded inside))

theorem sized_extract (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (start length : Nat) (bounded : length < 2 ^ 64) (above : j.toNat + 32 ≤ start)
    (inside : start + length ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k (z :: tail)).memory.extract start (start + length) = (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.extract start (start + length) := by
  rw [NativeSourceContextSizedBytes.length_word]
  exact word_extract (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).toMachineState j ((b - c) + UInt256.lnot (UInt256.ofNat 31))
    start length bounded above inside

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (firstSource : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size)
    (firstPadding : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat - (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (firstBelow : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat)
    (bounded : (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (storePadding : (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat - (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (below : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (endBound : ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)).toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat + (UInt256.ofNat 32).toNat < 2 ^ 256)
    (above : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat + 32 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (allocatorAbove : 96 ≤ (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat)
    (sourceAbove : 96 ≤ h.toNat)
    (fourthInside : h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size)
    (wordBelow : j.toNat + 32 ≤ h.toNat) :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding (NativeSourceSecondPayload.output (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)).toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat = (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.extract h.toNat (h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) := by
  have fits : j.toNat + 32 ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size := by omega
  have padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits := by
    have positive : 0 < 2 ^ System.Platform.numBits := Nat.pow_pos (by decide)
    omega
  have sizedInside := fourthInside.trans (NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k (z :: tail) padding)
  have bytes := NativeSourceContextSourceExtract.readback cost pre a b c d e f g h i j k z tail
    firstSource firstPadding firstBelow bounded storePadding below endBound above allocatorAbove sourceAbove sizedInside
  exact bytes.trans (sized_extract cost pre a b c d e f g h i j k z tail h.toNat (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat bounded wordBelow fourthInside)

end Compiler.Proofs.IRGeneration.NativeSourceContextFieldSourceExtract
