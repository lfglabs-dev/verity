import Compiler.Proofs.IRGeneration.NativeSourceFinalRoundingFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceSizedPackingMemory
open EvmYul

theorem size_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256) (tail : Stack UInt256) :
    (NativeSourcePackingSize.s6 cost pre a b c d e f g h tail).memory =
      (pre.toMachineState.mstore ((a + b) + c) h).memory := by
  rfl

theorem read_below (cost : Nat) (pre : EVM.State) (a b c d e f g h : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (padding : ((a + b) + c).toNat - pre.memory.size < 2 ^ System.Platform.numBits)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (inside : start + count ≤ pre.memory.size) (below : start + count ≤ ((a + b) + c).toNat) :
    (NativeSourcePackingSize.s6 cost pre a b c d e f g h tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  rw [size_memory]
  exact NativeSourceStoreFrame.read_below pre.toMachineState ((a + b) + c) h start count
    padding positive bounded inside below

end Compiler.Proofs.IRGeneration.NativeSourceSizedPackingMemory
