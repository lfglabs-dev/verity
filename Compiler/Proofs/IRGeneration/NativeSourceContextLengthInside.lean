import Compiler.Proofs.IRGeneration.NativeSourceContextCopyActive
import Compiler.Proofs.IRGeneration.NativeSourcePreservedLengthInside

namespace Compiler.Proofs.IRGeneration.NativeSourceContextLengthInside
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
    (wordInside : j.toNat + 32 ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size)
    (below : j.toNat + 32 ≤ (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat)
    (padding : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat - (copied cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits)
    (address : (((free cost pre a b c d e f g h i j k z tail) + (length cost pre a b c d e f g h i j k z tail)) + UInt256.ofNat 32).toNat < 2 ^ 64)
    (active : ¬j ≥ (copied cost pre a b c d e f g h i j k z tail).activeWords * ⟨32⟩)
    (source : h.toNat + ((copied cost pre a b c d e f g h i j k z tail).toMachineState.lookupMemory j).toNat ≤ (copied cost pre a b c d e f g h i j k z tail).memory.size) :
    h.toNat + (NativeSourceContextPacked.second_amount cost pre a b c d e f g h i j k z tail).toNat ≤
      (NativeSourceSecondCopyStore.loaded cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32)
        (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail) ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail).memory.size := by
  have bounded := NativeSourceContextCopyActive.copied_bound cost pre a b c d e f g h i j k z tail
    upper sd se sf sg fields sizeAddress lengthAddress destBound sourceBound countBound
  exact NativeSourcePreservedLengthInside.inside cost (copied cost pre a b c d e f g h i j k z tail) (length cost pre a b c d e f g h i j k z tail) j h (UInt256.ofNat 32)
    (free cost pre a b c d e f g h i j k z tail) (UInt256.ofNat 681) (free cost pre a b c d e f g h i j k z tail) ((free cost pre a b c d e f g h i j k z tail) + UInt256.ofNat 32) (UInt256.ofNat 0) z tail
    wordInside below padding bounded address active source

end Compiler.Proofs.IRGeneration.NativeSourceContextLengthInside
