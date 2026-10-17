import Compiler.Proofs.IRGeneration.NativeSourceAllocatorExtent
namespace Compiler.Proofs.IRGeneration.NativeSourcePreallocatorFree
open EvmYul
theorem context_free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits)
    (upper : (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat <
      2 ^ 251) :
    NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail) =
      j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  apply NativeSourcePointerExtent.context_free cost pre a b c d e f g h i j k tail padding
  exact NativeSourceAllocatorExtent.context_bound cost pre a b c d e f g h i j k tail upper

end Compiler.Proofs.IRGeneration.NativeSourcePreallocatorFree
