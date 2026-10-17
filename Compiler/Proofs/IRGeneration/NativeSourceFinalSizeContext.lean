import Compiler.Proofs.IRGeneration.NativeSourceSizedPackingMemory

namespace Compiler.Proofs.IRGeneration.NativeSourceFinalSizeContext
open EvmYul

def finish (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256) (tail : Stack UInt256) :=
  ((e + length) + ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)) + d

theorem read_below (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : (finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size)
    (below : start + count ≤ (finish cost pre length b c d e f g dest x y tail).toNat) :
    (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding start count := by
  unfold NativeSourceSizedSecondCopy.sized
  exact NativeSourceSizedPackingMemory.read_below cost
    (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail)
    (e + length) ((NativeSourceSecondCopyStore.stored cost pre length b c d e f g dest x y tail).toMachineState.lookupMemory b)
    d e f g dest x (y :: tail) start count padding positive bounded inside below

theorem carrier (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256)
    (padding : (finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size =
      max (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size
        ((finish cost pre length b c d e f g dest x y tail).toNat + 32) := by
  unfold NativeSourceSizedSecondCopy.sized
  rw [NativeSourceSizedPackingMemory.size_memory]
  exact MachineState.size_memory_mstore_of_pad _ _ x padding

theorem rounded_read (cost : Nat) (pre : EVM.State) (length b c d e f g dest x y : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : (finish cost pre length b c d e f g dest x y tail).toNat -
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.size)
    (below : start + count ≤ (finish cost pre length b c d e f g dest x y tail).toNat)
    (above : g.toNat + 32 ≤ start) :
    (NativeSourceRoundedSecondCopy.rounded cost pre length b c d e f g dest x y tail).memory.readWithPadding start count =
      (NativeSourceSecondPacking.packed cost pre length b c d e f g dest x y tail).memory.readWithPadding start count := by
  have insideSized : start + count ≤ (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail).memory.size := by
    rw [carrier cost pre length b c d e f g dest x y tail padding]
    exact inside.trans (Nat.le_max_left _ _)
  have frame := NativeSourceFinalRoundingFrame.read_above cost
    (NativeSourceSizedSecondCopy.sized cost pre length b c d e f g dest x y tail)
    ((finish cost pre length b c d e f g dest x y tail) - e) f g dest (x :: y :: tail)
    start count positive bounded above insideSized
  exact frame.trans (read_below cost pre length b c d e f g dest x y tail start count padding positive bounded inside below)

end Compiler.Proofs.IRGeneration.NativeSourceFinalSizeContext
