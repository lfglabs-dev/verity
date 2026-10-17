import Compiler.Proofs.IRGeneration.NativeSourcePackedEndBound
namespace Compiler.Proofs.IRGeneration.NativeSourceGuardedOriginalReturn
open EvmYul
theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256)
    (bounded : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)

    (secondSource : h.toNat + ((NativeSourceSecondCopyStore.stored cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).toMachineState.lookupMemory j).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.size)

    (above : 64 ≤ (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat)

    (sourceAbove : 96 ≤ i.toNat)
    (platform : 64 ≤ System.Platform.numBits)
    (inside0 : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ pre.memory.size)
    (fields : c.toNat + 288 < 2 ^ 64)
    (below0 : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ (c + UInt256.ofNat 192).toNat)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (below4 : i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat ≤ j.toNat)
    (endBound : (((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail).toNat +
      (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat) +
      (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat) + 32 + 31 < 2 ^ 256)
    (guard : NativeSourceAllocatorDecision.flag (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail)
      (NativeSourceContextPacked.requested cost pre a b c d e f g h i j k z tail) = ⟨0⟩)
 :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat =
      pre.memory.extract i.toNat (i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat) := by
  have bound := NativeSourcePackedEndBound.natural_end cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail endBound guard
  have first := NativeSourceAddressGeometry.add_toNat (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) (by omega)
  have output := NativeSourceAddressGeometry.add_toNat ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)) (UInt256.ofNat 32) (by omega)
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding := NativeSourceBoundedPadding.padding_of_address
    (((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size (by omega)
  have finalPadding := NativeSourcePackedEndBound.final_padding cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail
    (NativeSourceSecondPacking.packed cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681)
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory platform endBound guard
  exact NativeSourceOriginalContainedReturn.readback cost pre a b c d e f g h i j k z tail
    bounded padding secondSource finalPadding above sourceAbove platform inside0 fields below0 sizeBelow below4
    endBound guard

end Compiler.Proofs.IRGeneration.NativeSourceGuardedOriginalReturn
