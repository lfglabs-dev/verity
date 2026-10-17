import Compiler.Proofs.IRGeneration.NativeSourceFieldMemorySize

namespace Compiler.Proofs.IRGeneration.NativeSourceContextFieldFrames
open EvmYul

theorem loaded_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail).memory = pre.memory := by
  change (NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).memory = _
  exact (NativeSourceReturnShuffles.memory cost
    (NativeSourceZeroShuffles.s6 cost pre a b c d e f g h i j k tail)
    a g a b c d e f i h j (k :: UInt256.ofNat 0 :: tail)).trans
    (NativeSourceZeroShuffles.memory cost pre a b c d e f g h i j k tail)

theorem first (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size)
    (below : start + length ≤ (c + UInt256.ofNat 192).toNat) :
    (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  rw [← loaded_memory cost pre a b c d e f g h i j k tail] at padding inside ⊢
  exact NativeSourceFirstFieldFrame.read_below cost (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d)
    e f a g a b c (UInt256.ofNat 632)
    (h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) start length padding positive bounded inside below

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (c + UInt256.ofNat 224).toNat - (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size)
    (below : start + length ≤ (c + UInt256.ofNat 224).toNat) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length := by
  exact NativeSourceFirstFieldFrame.second_read_below cost (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e)
    f a g a b c (UInt256.ofNat 632) h
    (UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) start length padding positive bounded inside below

theorem third (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (c + UInt256.ofNat 256).toNat - (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size)
    (below : start + length ≤ (c + UInt256.ofNat 256).toNat) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length := by
  exact NativeSourceFirstFieldFrame.third_read_below cost (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail)
    (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a)
    g a b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) start length padding positive bounded inside below

theorem fourth (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : (c + UInt256.ofNat 288).toNat - (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size)
    (below : start + length ≤ (c + UInt256.ofNat 288).toNat) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length =
      (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.readWithPadding start length := by
  exact NativeSourceFirstFieldFrame.fourth_read_below cost (NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail)
    (((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j
    (k :: UInt256.ofNat 0 :: tail) start length padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceContextFieldFrames
