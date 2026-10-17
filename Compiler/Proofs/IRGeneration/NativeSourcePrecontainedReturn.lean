import Compiler.Proofs.IRGeneration.NativeSourceEntryContainedReturn
import Compiler.Proofs.IRGeneration.NativeSourceGeometricSecondReturn
import Compiler.Proofs.IRGeneration.NativeSourceSeparatedReturn
import Compiler.Proofs.IRGeneration.NativeSourceCarrierDerivedReturn
import Compiler.Proofs.IRGeneration.NativeSourceActiveDerivedReturn
import Compiler.Proofs.IRGeneration.NativeSourceDerivedSecondReturn
import Compiler.Proofs.IRGeneration.NativeSourceGuardedOriginalReturn

namespace Compiler.Proofs.IRGeneration.NativeSourcePrecontainedReturn
open EvmYul NativeSourceContextCopy

theorem carrier_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 64 ≤ System.Platform.numBits)
    (fields : c.toNat + 288 < 2 ^ 64) (memoryAbove : 96 ≤ pre.memory.size)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32) :
    pre.memory.size ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size := by
  have power : 2 ^ 64 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  have first := NativeSourceBoundedPadding.field_padding c pre.memory (by omega) (by omega)
  have p1 := NativeSourceFieldPadding.second_padding cost pre a b c d e f g h i j k tail (by omega) first
  have p2 := NativeSourceFieldPadding.third_padding cost pre a b c d e f g h i j k tail (by omega) p1
  have p3 := NativeSourceFieldPadding.fourth_padding cost pre a b c d e f g h i j k tail (by omega) p2
  have p4 := NativeSourceSizePadding.size_padding_from_first cost pre a b c d e f g h i j k tail
    (by omega) first sizeBelow
  have m1 := NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k tail first
  have m2 := NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k tail p1
  have m3 := NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k tail p2
  have m4 := NativeSourceContextMemorySize.fourth cost pre a b c d e f g h i j k tail p3
  have m5 := NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k tail p4
  rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k tail (by omega)]
  exact m1.trans (m2.trans (m3.trans (m4.trans m5)))

theorem readback (cost : Nat)
    (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256)
    (bounded : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
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
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64)
    (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64)
    (sg : g.toNat < 2 ^ 64)
    (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩)
    (sizeAbove : 96 ≤ j.toNat)
    (ordered : c.toNat + 32 ≤ b.toNat)
    (sourceValue : h.toNat = c.toNat + 32)
    (finishOriginal : b.toNat ≤ pre.memory.size) :
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat =
      pre.memory.extract i.toNat (i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat) := by
  have finishEntry := finishOriginal.trans
    (carrier_monotone cost pre a b c d e f g h i j k (z :: tail) platform fields (by omega) sizeBelow)
  exact NativeSourceEntryContainedReturn.readback cost pre a b c d e f g h i j k z tail
    bounded above sourceAbove platform inside0 fields below0 sizeBelow below4 endBound guard
    upper sd se sf sg sizeAddress lengthAddress destBound sourceBound firstGuard sizeAbove
    ordered sourceValue finishEntry

end Compiler.Proofs.IRGeneration.NativeSourcePrecontainedReturn
