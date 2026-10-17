import Compiler.Proofs.IRGeneration.NativeSourceActiveDerivedReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceSizewordCarrier
open EvmYul

theorem sized_inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    j.toNat + 32 ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size := by
  have size := NativeSourceSizeCarrier.size cost
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail) padding
  change j.toNat + 32 ≤ (NativeSourceFieldSize.stored cost
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail)).memory.size
  rw [size]
  exact Nat.le_max_right _ _

theorem returned_inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (above : 64 ≤ j.toNat)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    j.toNat + 32 ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size := by
  have inside := sized_inside cost pre a b c d e f g h i j k tail padding
  rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k tail (by omega)]
  exact inside

end Compiler.Proofs.IRGeneration.NativeSourceSizewordCarrier
