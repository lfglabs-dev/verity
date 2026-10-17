import Compiler.Proofs.IRGeneration.NativeSourceSizePadding

namespace Compiler.Proofs.IRGeneration.NativeSourceSizedPaddingCopy
open EvmYul

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) (count : Nat)
    (above : 96 ≤ i.toNat)
    (bounded : count < 2 ^ 64)
    (padding0 : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside0 : i.toNat + count ≤ pre.memory.size)
    (fieldFits : c.toNat + 288 < 2 ^ 256)
    (below0 : i.toNat + count ≤ (c + UInt256.ofNat 192).toNat)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32)
    (below4 : i.toNat + count ≤ j.toNat)
    (extent : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat = count)
    (copyPadding : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat count =
      pre.memory.extract i.toNat (i.toNat + count) := by
  have padding4 := NativeSourceSizePadding.size_padding_from_first cost pre a b c d e f g h i j k
    (z :: tail) fieldFits padding0 sizeBelow
  exact NativeSourceDerivedPaddingCopy.readback cost pre a b c d e f g h i j k z tail count
    above bounded padding0 inside0 fieldFits below0 padding4 below4 extent copyPadding

end Compiler.Proofs.IRGeneration.NativeSourceSizedPaddingCopy
