import Compiler.Proofs.IRGeneration.NativeSourceContextActiveGuard
import Compiler.Proofs.IRGeneration.NativeSourceDerivedSecondReturn
import Compiler.Proofs.IRGeneration.NativeSourceGuardedOriginalReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceActiveDerivedReturn
open EvmYul NativeSourceContextCopy

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
    (wordInside : j.toNat + 32 ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size)
    (below : j.toNat + 32 ≤ (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat)
    (source : h.toNat + ((copied cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j).toNat ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size):
    (NativeSourcePackedAllocation.returned cost (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail) (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.readWithPadding ((NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32).toNat (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat =
      pre.memory.extract i.toNat (i.toNat + (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat) := by
  have active := NativeSourceContextActiveGuard.copied_guard cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound bounded
  exact NativeSourceDerivedSecondReturn.readback cost pre a b c d e f g h i j k z tail
    bounded above sourceAbove platform inside0 fields below0 sizeBelow below4 endBound guard
    upper sd se sf sg sizeAddress lengthAddress destBound sourceBound wordInside below active source

end Compiler.Proofs.IRGeneration.NativeSourceActiveDerivedReturn
