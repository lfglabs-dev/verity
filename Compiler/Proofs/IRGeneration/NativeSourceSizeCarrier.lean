import Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSizeCarrier
open EvmYul

theorem store_size (cost : Nat) (pre : EVM.State) (mask size a b c d e f g : UInt256)
    (tail : Stack UInt256)
    (padding : f.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldRoundingStore.s4 cost pre mask size a b c d e f g tail).memory.size =
      max pre.memory.size (f.toNat + 32) := by
  have result := MachineState.size_memory_mstore_of_pad
    (NativeSourceFieldRoundingStore.s3 cost pre mask size a b c d e f g tail).toMachineState
    f (size + mask)
  rw [NativeSourceSizeMemoryFrame.shuffle_memory] at result
  exact result padding

theorem size (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256)
    (padding : h.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).memory.size =
      max pre.memory.size (h.toNat + 32) := by
  have result := store_size cost (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail)
    (UInt256.lnot (UInt256.ofNat 31)) (a - b) c d e f g h i tail
  rw [NativeSourceSizeMemoryFrame.ready_memory] at result
  exact result padding

theorem monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256)
    (padding : h.toNat - pre.memory.size < 2 ^ System.Platform.numBits) :
    pre.memory.size ≤ (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).memory.size := by
  rw [size cost pre a b c d e f g h i tail padding]
  exact Nat.le_max_left _ _

theorem context_monotone (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : j.toNat - (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits) :
    (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).memory.size ≤
      (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size := by
  exact monotone cost (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail)
    b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i (UInt256.ofNat 681) j k
    (UInt256.ofNat 0 :: tail) padding

end Compiler.Proofs.IRGeneration.NativeSourceSizeCarrier
