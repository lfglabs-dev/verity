import Compiler.Proofs.IRGeneration.NativeSourceSizedWindowFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturnFrame
open EvmYul

theorem pushed_memory (cost : Nat) (pre : EVM.State) :
    (NativeSourceAllocatorReturn.pushed cost pre).memory = pre.memory := by
  rfl

theorem returned_memory (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory =
      (NativeSourceAllocatorReturn.stored cost pre pointer target tail).memory := by
  rfl

theorem read_above (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256)
    (start length : Nat)
    (positive : 0 < length) (bounded : length < 2 ^ 64)
    (above : 96 ≤ start) (inside : start + length ≤ pre.memory.size) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory.readWithPadding start length =
      pre.memory.readWithPadding start length := by
  have fits : 96 ≤ pre.memory.size := by omega
  rw [returned_memory]
  exact NativeSourceMemoryFrame.read_above
    (NativeSourceAllocatorReturn.pushed cost pre).toMachineState (UInt256.ofNat 64) pointer
    start length fits positive bounded above inside

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorReturnFrame
