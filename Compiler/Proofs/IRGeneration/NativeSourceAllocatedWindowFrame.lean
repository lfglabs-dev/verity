import Compiler.Proofs.IRGeneration.NativeSourceSizeCarrier

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatedWindowFrame
open EvmYul

theorem preserve (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (above : 96 ≤ start)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (padding0 : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (inside0 : start + length ≤ pre.memory.size)
    (below0 : start + length ≤ (c + UInt256.ofNat 192).toNat)
    (padding1 : (c + UInt256.ofNat 224).toNat - (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (below1 : start + length ≤ (c + UInt256.ofNat 224).toNat)
    (padding2 : (c + UInt256.ofNat 256).toNat - (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (below2 : start + length ≤ (c + UInt256.ofNat 256).toNat)
    (padding3 : (c + UInt256.ofNat 288).toNat - (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (below3 : start + length ≤ (c + UInt256.ofNat 288).toNat)
    (padding4 : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (below4 : start + length ≤ j.toNat)
    : (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have inside1 := inside0.trans (NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k tail padding0)
  have inside2 := inside1.trans (NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k tail padding1)
  have inside3 := inside2.trans (NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k tail padding2)
  have inside4 := inside3.trans (NativeSourceContextMemorySize.fourth cost pre a b c d e f g h i j k tail padding3)
  have inside5 := inside4.trans (NativeSourceSizeCarrier.context_monotone cost pre a b c d e f g h i j k tail padding4)
  rw [NativeSourceFirstAllocatorFrame.context_read_above cost pre a b c d e f g h i j k tail start length
    positive bounded above inside5]
  exact NativeSourceSizedWindowFrame.preserve cost pre a b c d e f g h i j k tail start length
    positive bounded padding0 inside0 below0 padding1 below1 padding2 below2 padding3 below3 padding4 below4

end Compiler.Proofs.IRGeneration.NativeSourceAllocatedWindowFrame
