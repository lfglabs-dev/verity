import Compiler.Proofs.IRGeneration.NativeSourceDerivedPaddingCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceSizePadding
open EvmYul

theorem fourth_extent (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 288).toNat -
      (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (c + UInt256.ofNat 288).toNat + 32 ≤
      (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  have size : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size =
      max (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size
        ((c + UInt256.ofNat 288).toNat + 32) := by
    exact NativeSourceFieldMemorySize.fourth_size cost (NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail)
      (((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a)
      b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j
      (k :: UInt256.ofNat 0 :: tail) padding
  rw [size]
  exact Nat.le_max_right _ _

theorem size_padding (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 288).toNat -
      (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (below : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32) :
    j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits := by
  have inside := fourth_extent cost pre a b c d e f g h i j k tail padding
  rw [Nat.sub_eq_zero_of_le (below.trans inside)]
  exact Nat.two_pow_pos _

theorem size_padding_from_first (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (fits : c.toNat + 288 < 2 ^ 256)
    (padding : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (below : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32) :
    j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits := by
  have padding1 := NativeSourceFieldPadding.second_padding cost pre a b c d e f g h i j k tail fits padding
  have padding2 := NativeSourceFieldPadding.third_padding cost pre a b c d e f g h i j k tail fits padding1
  have padding3 := NativeSourceFieldPadding.fourth_padding cost pre a b c d e f g h i j k tail fits padding2
  exact size_padding cost pre a b c d e f g h i j k tail padding3 below

end Compiler.Proofs.IRGeneration.NativeSourceSizePadding

