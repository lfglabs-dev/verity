import Compiler.Proofs.IRGeneration.NativeSourceContainedOriginalReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSourceInside
open EvmYul

theorem inside (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (count : Nat) (above : 96 ≤ i.toNat)
    (original : i.toNat + count ≤ pre.memory.size)
    (fits : c.toNat + 288 < 2 ^ 256)
    (padding : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (sizeBelow : j.toNat ≤ (c + UInt256.ofNat 288).toNat + 32) :
    i.toNat + count ≤ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size := by
  have p1 := NativeSourceFieldPadding.second_padding cost pre a b c d e f g h i j k tail fits padding
  have p2 := NativeSourceFieldPadding.third_padding cost pre a b c d e f g h i j k tail fits p1
  have p3 := NativeSourceFieldPadding.fourth_padding cost pre a b c d e f g h i j k tail fits p2
  have p4 := NativeSourceSizePadding.size_padding_from_first cost pre a b c d e f g h i j k tail fits padding sizeBelow
  have i1 := original.trans (NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k tail padding)
  have i2 := i1.trans (NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k tail p1)
  have i3 := i2.trans (NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k tail p2)
  have i4 := i3.trans (NativeSourceContextMemorySize.fourth cost pre a b c d e f g h i j k tail p3)
  have i5 := i4.trans (NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k tail p4)
  rw [NativeSourceAllocatorCarrier.context_size cost pre a b c d e f g h i j k tail (by omega)]
  exact i5

end Compiler.Proofs.IRGeneration.NativeSourceContextSourceInside
