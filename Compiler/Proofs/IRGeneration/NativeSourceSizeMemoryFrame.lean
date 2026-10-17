import Compiler.Proofs.IRGeneration.NativeSourceOriginalWindowFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSizeMemoryFrame
open EvmYul

theorem shuffle_memory (cost : Nat) (pre : EVM.State)
    (mask size a b c d e f g : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldRoundingStore.s3 cost pre mask size a b c d e f g tail).memory = pre.memory := by
  rfl

theorem masked_memory (cost : Nat) (pre : EVM.State) :
    (NativeSourceFieldRoundingEntry.masked cost pre).memory = pre.memory := by
  rfl

theorem sized_memory (cost : Nat) (pre : EVM.State) (a b : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldSizeEntry.sized cost pre a b tail).memory = pre.memory := by
  rfl

theorem ready_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) :
    (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail).memory = pre.memory := by
  unfold NativeSourceFieldSize.ready
  rw [masked_memory, sized_memory]

theorem store_read_below (cost : Nat) (pre : EVM.State)
    (mask size a b c d e f g : UInt256) (tail : Stack UInt256) (start length : Nat)
    (padding : f.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ f.toNat) :
    (NativeSourceFieldRoundingStore.s4 cost pre mask size a b c d e f g tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have frame := NativeSourceStoreFrame.read_below
    (NativeSourceFieldRoundingStore.s3 cost pre mask size a b c d e f g tail).toMachineState
    f (size + mask) start length
  rw [shuffle_memory] at frame
  exact frame padding positive bounded inside below

theorem read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (start length : Nat)
    (padding : h.toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (inside : start + length ≤ pre.memory.size) (below : start + length ≤ h.toNat) :
    (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have frame := store_read_below cost (NativeSourceFieldSize.ready cost pre a b c d e f g h i tail)
    (UInt256.lnot (UInt256.ofNat 31)) (a - b) c d e f g h i tail start length
  rw [ready_memory] at frame
  exact frame padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceSizeMemoryFrame
