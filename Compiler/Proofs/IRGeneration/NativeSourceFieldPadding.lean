import Compiler.Proofs.IRGeneration.NativeSourceGeometricOriginalCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldPadding
open EvmYul

theorem next_padding (machine : MachineState) (address value next : UInt256)
    (padding : address.toNat - machine.memory.size < 2 ^ System.Platform.numBits)
    (adjacent : next.toNat = address.toNat + 32) :
    next.toNat - (machine.mstore address value).memory.size < 2 ^ System.Platform.numBits := by
  have inside := MachineState.le_size_memory_mstore machine address value padding
  rw [adjacent, Nat.sub_eq_zero_of_le inside]
  exact Nat.two_pow_pos _

theorem second_padding (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (fits : c.toNat + 288 < 2 ^ 256)
    (padding : (c + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (c + UInt256.ofNat 224).toNat -
      (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits := by
  have first := NativeSourceFieldGeometry.offset_toNat c 192 (by decide) (by omega)
  have second := NativeSourceFieldGeometry.offset_toNat c 224 (by decide) (by omega)
  have size : (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size =
      max pre.memory.size ((c + UInt256.ofNat 192).toNat + 32) := by
    have frame := NativeSourceFieldMemorySize.first_size cost
      (NativeSourceFieldLoad.loaded cost pre a b c d e f g h i j k tail)
      ((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d)
      e f a g a b c (UInt256.ofNat 632)
      (h :: UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail)
    rw [NativeSourceContextFieldFrames.loaded_memory] at frame
    exact frame padding
  rw [size, Nat.sub_eq_zero_of_le (by omega)]
  exact Nat.two_pow_pos _

theorem third_padding (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (fits : c.toNat + 288 < 2 ^ 256)
    (padding : (c + UInt256.ofNat 224).toNat -
      (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (c + UInt256.ofNat 256).toNat -
      (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits := by
  have first := NativeSourceFieldGeometry.offset_toNat c 224 (by decide) (by omega)
  have second := NativeSourceFieldGeometry.offset_toNat c 256 (by decide) (by omega)
  have size : (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size =
      max (NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).memory.size
        ((c + UInt256.ofNat 224).toNat + 32) := by
    exact NativeSourceFieldMemorySize.second_size cost
      (NativeSourceSecondFieldLoad.loaded cost pre a b c d e f g h i j k tail)
      ((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e)
      f a g a b c (UInt256.ofNat 632) h
      (UInt256.ofNat 32 :: i :: UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) padding
  rw [size, Nat.sub_eq_zero_of_le (by omega)]
  exact Nat.two_pow_pos _

theorem fourth_padding (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256) (fits : c.toNat + 288 < 2 ^ 256)
    (padding : (c + UInt256.ofNat 256).toNat -
      (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits) :
    (c + UInt256.ofNat 288).toNat -
      (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size < 2 ^ System.Platform.numBits := by
  have first := NativeSourceFieldGeometry.offset_toNat c 256 (by decide) (by omega)
  have second := NativeSourceFieldGeometry.offset_toNat c 288 (by decide) (by omega)
  have size : (NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).memory.size =
      max (NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).memory.size
        ((c + UInt256.ofNat 256).toNat + 32) := by
    exact NativeSourceFieldMemorySize.third_size cost
      (NativeSourceMaskedContext.ready cost pre a b c d e f g h i j k tail)
      (((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a)
      g a b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
      (UInt256.ofNat 681 :: j :: k :: UInt256.ofNat 0 :: tail) padding
  rw [size, Nat.sub_eq_zero_of_le (by omega)]
  exact Nat.two_pow_pos _

end Compiler.Proofs.IRGeneration.NativeSourceFieldPadding


