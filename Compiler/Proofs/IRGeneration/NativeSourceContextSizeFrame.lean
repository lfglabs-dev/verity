import Compiler.Proofs.IRGeneration.NativeSourceSizeMemoryFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceContextSizeFrame
open EvmYul

theorem read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size)
    (below : start + length ≤ j.toNat) :
    (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length := by
  unfold NativeSourceSizedFields.stored
  exact NativeSourceSizeMemoryFrame.read_below cost
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail) start length padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceContextSizeFrame
