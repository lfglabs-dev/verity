import Compiler.Proofs.IRGeneration.NativeSourceSizeFieldExtent

namespace Compiler.Proofs.IRGeneration.NativeSourceOriginalFree
open EvmYul

theorem pointer_padding (memory : ByteArray) (platform : 7 ≤ System.Platform.numBits) :
    64 - memory.size < 2 ^ System.Platform.numBits := by
  have bound : 2 ^ 7 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) platform
  omega

theorem context_free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (platform : 7 ≤ System.Platform.numBits)
    (upper : pre.activeWords.toNat < 2 ^ 251)
    (sd : d.toNat < 2 ^ 64) (se : e.toNat < 2 ^ 64)
    (sf : f.toNat < 2 ^ 64) (sg : g.toNat < 2 ^ 64)
    (d1 : (c + UInt256.ofNat 192).toNat < 2 ^ 64)
    (d2 : (c + UInt256.ofNat 224).toNat < 2 ^ 64)
    (d3 : (c + UInt256.ofNat 256).toNat < 2 ^ 64)
    (d4 : (c + UInt256.ofNat 288).toNat < 2 ^ 64) (sizeAddress : j.toNat < 2 ^ 64) :
    NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail) =
      j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  apply NativeSourcePreallocatorFree.context_free cost pre a b c d e f g h i j k tail
  · exact pointer_padding _ platform
  · exact NativeSourceSizeFieldExtent.all_fields_bound cost pre a b c d e f g h i j k tail
      upper sd se sf sg d1 d2 d3 d4 sizeAddress

end Compiler.Proofs.IRGeneration.NativeSourceOriginalFree
