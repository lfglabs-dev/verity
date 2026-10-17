import Compiler.Proofs.IRGeneration.NativeSourceContextMemorySize

namespace Compiler.Proofs.IRGeneration.NativeSourceOriginalWindowFrame
open EvmYul

theorem preserve (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
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
    : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have inside1 := inside0.trans (NativeSourceContextMemorySize.first cost pre a b c d e f g h i j k tail padding0)
  have inside2 := inside1.trans (NativeSourceContextMemorySize.second cost pre a b c d e f g h i j k tail padding1)
  have inside3 := inside2.trans (NativeSourceContextMemorySize.third cost pre a b c d e f g h i j k tail padding2)
  rw [NativeSourceContextFieldFrames.fourth cost pre a b c d e f g h i j k tail start length padding3 positive bounded inside3 below3]
  rw [NativeSourceContextFieldFrames.third cost pre a b c d e f g h i j k tail start length padding2 positive bounded inside2 below2]
  rw [NativeSourceContextFieldFrames.second cost pre a b c d e f g h i j k tail start length padding1 positive bounded inside1 below1]
  rw [NativeSourceContextFieldFrames.first cost pre a b c d e f g h i j k tail start length padding0 positive bounded inside0 below0]

end Compiler.Proofs.IRGeneration.NativeSourceOriginalWindowFrame
