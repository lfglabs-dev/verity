import Compiler.Proofs.IRGeneration.NativeSourceFirstPayloadSurvival

namespace Compiler.Proofs.IRGeneration.NativeSourceFinalRoundingFrame
open EvmYul

theorem stored_memory (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256) (tail : Stack UInt256) :
    (NativeSourceRoundingStore.s4 cost pre mask size a b c tail).memory =
      (pre.toMachineState.mstore b (size + mask)).memory := by
  rfl

theorem masked_memory (cost : Nat) (pre : EVM.State) :
    (NativeSourceRoundingEntry.masked cost pre).memory = pre.memory := by
  rfl

theorem store_read_above (cost : Nat) (pre : EVM.State) (mask size a b c : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (above : b.toNat + 32 ≤ start) (inside : start + count ≤ pre.memory.size) :
    (NativeSourceRoundingStore.s4 cost pre mask size a b c tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  rw [stored_memory]
  exact NativeSourceMemoryFrame.read_above pre.toMachineState b (size + mask) start count
    (by omega) positive bounded above inside

theorem read_above (cost : Nat) (pre : EVM.State) (size a b c : UInt256)
    (tail : Stack UInt256) (start count : Nat)
    (positive : 0 < count) (bounded : count < 2 ^ 64)
    (above : b.toNat + 32 ≤ start) (inside : start + count ≤ pre.memory.size) :
    (NativeSourceRounding.rounded cost pre size a b c tail).memory.readWithPadding start count =
      pre.memory.readWithPadding start count := by
  have frame := store_read_above cost (NativeSourceRoundingEntry.masked cost pre)
    (UInt256.lnot (UInt256.ofNat 31)) size a b c tail start count positive bounded above
  rw [masked_memory] at frame
  exact frame inside

end Compiler.Proofs.IRGeneration.NativeSourceFinalRoundingFrame
