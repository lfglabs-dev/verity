import Compiler.Proofs.IRGeneration.NativeSourceSizewordSourceExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSecondSourceExtent
open EvmYul NativeSourceContextCopy

theorem inside (cost : Nat) (pre : EVM.State)
    (a b c d e f g h i j k z : UInt256) (tail : Stack UInt256)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (fields : c.toNat + 288 < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64)
    (lengthAddress : k.toNat < 2 ^ 64)
    (destBound : (free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat < 2 ^ 64)
    (sourceBound : i.toNat < 2 ^ 64)
    (countBound : (length cost pre a b c d e f g h i j k z tail).toNat < 2 ^ 64)
    (platform : 64 ≤ System.Platform.numBits) (sizeAbove : 96 ≤ j.toNat)
    (sourceAbove : 96 ≤ i.toNat) (original : i.toNat + (length cost pre a b c d e f g h i j k z tail).toNat ≤ pre.memory.size)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (firstGuard : NativeSourceAllocatorDecision.flag j (b - c) = ⟨0⟩)
    (ordered : c.toNat + 32 ≤ b.toNat)
    (sourceValue : h.toNat = c.toNat + 32)
    (finishInside : b.toNat ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size) :
    h.toNat + ((copied cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j).toNat ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size := by
  have value := NativeSourceContextSizewordValue.value cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
    platform sizeAbove sourceAbove original sizeBelow firstGuard
  rw [value, sourceValue, NativeSourceSizewordNatural.source_end b c ordered]
  exact finishInside

end Compiler.Proofs.IRGeneration.NativeSourceContextSecondSourceExtent
