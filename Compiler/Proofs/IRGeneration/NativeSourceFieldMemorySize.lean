import Compiler.Proofs.IRGeneration.NativeSourceFirstFieldFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldMemorySize
open EvmYul

theorem first_size (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (h + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldStore.s4 cost pre a b c d e f g h i tail).memory.size =
      max pre.memory.size ((h + UInt256.ofNat 192).toNat + 32) := by
  exact MachineState.size_memory_mstore_of_pad
    (NativeSourceFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (h + UInt256.ofNat 192) a padding

theorem first_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (h + UInt256.ofNat 192).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceFieldStore.s4 cost pre a b c d e f g h i tail).memory.size := by
  rw [first_size cost pre a b c d e f g h i tail padding]
  exact Nat.le_max_left _ _

theorem second_size (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (g + UInt256.ofNat 224).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSecondFieldStore.s4 cost pre a b c d e f g h i tail).memory.size =
      max pre.memory.size ((g + UInt256.ofNat 224).toNat + 32) := by
  exact MachineState.size_memory_mstore_of_pad
    (NativeSourceSecondFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (g + UInt256.ofNat 224) a padding

theorem second_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (g + UInt256.ofNat 224).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceSecondFieldStore.s4 cost pre a b c d e f g h i tail).memory.size := by
  rw [second_size cost pre a b c d e f g h i tail padding]
  exact Nat.le_max_left _ _

theorem third_size (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (e + UInt256.ofNat 256).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceMaskedFieldStore.s4 cost pre a b c d e f g h i tail).memory.size =
      max pre.memory.size ((e + UInt256.ofNat 256).toNat + 32) := by
  exact MachineState.size_memory_mstore_of_pad
    (NativeSourceMaskedFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (e + UInt256.ofNat 256) a padding

theorem third_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (e + UInt256.ofNat 256).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceMaskedFieldStore.s4 cost pre a b c d e f g h i tail).memory.size := by
  rw [third_size cost pre a b c d e f g h i tail padding]
  exact Nat.le_max_left _ _

theorem fourth_size (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 288).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFourthFieldStore.s4 cost pre a b c d e f g h i tail).memory.size =
      max pre.memory.size ((c + UInt256.ofNat 288).toNat + 32) := by
  exact MachineState.size_memory_mstore_of_pad
    (NativeSourceFourthFieldStore.s3 cost pre a b c d e f g h i tail).toMachineState
    (c + UInt256.ofNat 288) a padding

theorem fourth_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256) (tail : Stack UInt256)
    (padding : (c + UInt256.ofNat 288).toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceFourthFieldStore.s4 cost pre a b c d e f g h i tail).memory.size := by
  rw [fourth_size cost pre a b c d e f g h i tail padding]
  exact Nat.le_max_left _ _

end Compiler.Proofs.IRGeneration.NativeSourceFieldMemorySize
