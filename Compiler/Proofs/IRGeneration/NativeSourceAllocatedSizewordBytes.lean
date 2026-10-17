import Compiler.Proofs.IRGeneration.NativeSourceSizewordBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatedSizewordBytes
open EvmYul

theorem bytes (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (above : 96 ≤ j.toNat)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.readWithPadding j.toNat 32 =
      ((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray := by
  rw [NativeSourceFirstAllocatorFrame.context_read_above cost pre a b c d e f g h i j k tail
    j.toNat 32 (by decide) (by decide) above
    (NativeSourceSizewordCarrier.sized_inside cost pre a b c d e f g h i j k tail padding)]
  exact NativeSourceSizewordBytes.context_bytes cost pre a b c d e f g h i j k tail padding

theorem lookup (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (above : 96 ≤ j.toNat)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (upper : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (address : j.toNat < 2 ^ 64) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory j =
      (b - c) + UInt256.lnot (UInt256.ofNat 31) := by
  apply NativeSourceWordRoundtrip.lookup_of_bytes
  · have inside := NativeSourceSizewordCarrier.returned_inside cost pre a b c d e f g h i j k tail (by omega) padding
    omega
  · exact NativeSourceAllocatorActiveGuard.sizeword_guard cost pre a b c d e f g h i j k tail upper address
  · exact bytes cost pre a b c d e f g h i j k tail above padding

end Compiler.Proofs.IRGeneration.NativeSourceAllocatedSizewordBytes
