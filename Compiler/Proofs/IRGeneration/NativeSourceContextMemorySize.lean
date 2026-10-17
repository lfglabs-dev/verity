import Compiler.Proofs.IRGeneration.NativeSourceAllFieldsFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceContextMemorySize
open EvmYul

theorem first (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  rw [← NativeSourceContextFieldFrames.loaded_memory cost pre a b c d e f g h i j k tail] at padding ⊢
  exact NativeSourceFieldMemorySize.first_monotone cost (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d)
    e f a g a b c (UInt256.ofNat 632)
    (h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) padding

theorem second (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 224).toNat - (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size ≤ (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  exact NativeSourceFieldMemorySize.second_monotone cost (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail)
    ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e)
    f a g a b c (UInt256.ofNat 632) h
    (UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) padding

theorem third (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 256).toNat - (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size ≤ (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  exact NativeSourceFieldMemorySize.third_monotone cost (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail)
    (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a)
    g a b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) padding

theorem fourth (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 288).toNat - (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size ≤ (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size := by
  exact NativeSourceFieldMemorySize.fourth_monotone cost (NativeSourceFourthContext.ready cost pre a b c d e f g h i j k tail)
    (((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j
    (k :: UInt256.ofNat 0 :: tail) padding

end Compiler.Proofs.IRGeneration.NativeSourceContextMemorySize
