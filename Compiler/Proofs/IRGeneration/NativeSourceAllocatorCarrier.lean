import Compiler.Proofs.IRGeneration.NativeSourceContextCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorCarrier
open EvmYul

theorem returned_size (cost : Nat) (pre : EVM.State) (pointer target : UInt256)
    (tail : Stack UInt256) (fits : 96 ≤ pre.memory.size) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory.size = pre.memory.size := by
  change ((EVM.Proof.stepPre cost (NativeSourceAllocatorReturn.pushed cost pre)).toMachineState.mstore
    (UInt256.ofNat 64) pointer).memory.size = _
  exact MachineState.size_memory_mstore _ _ _ fits

theorem success_size (cost : Nat) (pre : EVM.State) (base size target : UInt256)
    (tail : Stack UInt256) (fits : 96 ≤ pre.memory.size) :
    (NativeSourceAllocatorSuccess.returned cost pre base size target tail).memory.size = pre.memory.size := by
  unfold NativeSourceAllocatorSuccess.returned
  rw [returned_size]
  · rw [NativeSourceAllocatorPrefixMemory.decided]
  · rw [NativeSourceAllocatorPrefixMemory.decided]
    exact fits

theorem caller_size (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256)
    (tail : Stack UInt256) (fits : 96 ≤ pre.memory.size) :
    (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).memory.size = pre.memory.size := by
  unfold NativeSourceFirstAllocatorCaller.returned
  rw [success_size]
  · rw [NativeSourceFirstAllocatorFrame.entered_memory]
  · rw [NativeSourceFirstAllocatorFrame.entered_memory]
    exact fits

theorem context_size (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (fits : 96 ≤ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.size =
      (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size := by
  exact caller_size cost _ (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j (k :: UInt256.ofNat 0 :: tail) fits

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorCarrier
