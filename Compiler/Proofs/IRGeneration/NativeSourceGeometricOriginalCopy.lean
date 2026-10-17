import Compiler.Proofs.IRGeneration.NativeSourceFieldGeometry

namespace Compiler.Proofs.IRGeneration.NativeSourceGeometricOriginalCopy
open EvmYul

theorem readback (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k z : UInt256)
    (tail : Stack UInt256) (count : Nat)
    (above : 96 ≤ i.toNat)
    (bounded : count < 2 ^ 64)
    (padding0 : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside0 : i.toNat + count ≤ pre.memory.size)
    (fieldFits : c.toNat + 288 < 2 ^ 256)
    (below0 : i.toNat + count ≤ (c + UInt256.ofNat 192).toNat)
    (padding1 : (c + UInt256.ofNat 224).toNat - (NativeSourceFirstField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (padding2 : (c + UInt256.ofNat 256).toNat - (NativeSourceSecondField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (padding3 : (c + UInt256.ofNat 288).toNat - (NativeSourceThirdField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (padding4 : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k (z :: tail)).memory.size < 2 ^ System.Platform.numBits)
    (below4 : i.toNat + count ≤ j.toNat)
    (extent : (NativeSourceContextCopy.length cost pre a b c d e f g h i j k z tail).toNat = count)
    (copyPadding : (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat -
      (NativeSourceContextCopy.entry cost pre a b c d e f g h i j k z tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceContextCopy.copied cost pre a b c d e f g h i j k z tail).memory.readWithPadding
      (NativeSourceContextCopy.free cost pre a b c d e f g h i j k z tail + UInt256.ofNat 32).toNat count =
      pre.memory.extract i.toNat (i.toNat + count) := by
  have fields := NativeSourceFieldGeometry.fields_below c (i.toNat + count) fieldFits below0
  exact NativeSourceContextOriginalCopy.readback cost pre a b c d e f g h i j k z tail count
    above bounded padding0 inside0 below0 padding1 fields.1 padding2 fields.2.1
    padding3 fields.2.2 padding4 below4 extent copyPadding

end Compiler.Proofs.IRGeneration.NativeSourceGeometricOriginalCopy
