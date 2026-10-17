import Compiler.Proofs.IRGeneration.NativeSourceContextSourceInside
namespace Compiler.Proofs.IRGeneration.NativeSourceOriginalContainedReturn
open EvmYul
theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256)
    (bounded : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (padding : (((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail)) + (UInt256.ofNat 32)).toNat - (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (secondSource : h.toNat + ((NativeSourceSecondCopyStore.stored cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).toMachineState.lookupMemory j).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.size)
    (finalPadding : (NativeSourceFinalSizeContext.finish cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).toNat -
      (NativeSourceSecondPacking.packed cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.size < 2 ^ System.Platform.numBits)
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
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have padding0 := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have entrySource := NativeSourceContextSourceInside.inside cost pre a b c d e f g h i j k (z :: tail)
    (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat
    sourceAbove inside0 (by omega) padding0 sizeBelow
  exact NativeSourceContainedOriginalReturn.readback cost pre a b c d e f g h i j k z tail
    bounded padding secondSource finalPadding above sourceAbove platform inside0 fields below0 sizeBelow below4
    endBound guard entrySource

end Compiler.Proofs.IRGeneration.NativeSourceOriginalContainedReturn
