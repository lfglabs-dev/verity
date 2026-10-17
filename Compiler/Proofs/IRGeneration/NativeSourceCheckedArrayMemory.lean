import Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocationFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayMemory
open EvmYul EVM EVM.Proof

theorem mstore_memory (left right : MachineState) (offset word : UInt256)
    (same : left.memory = right.memory) :
    (left.mstore offset word).memory = (right.mstore offset word).memory := by
  change word.toByteArray.write 0 left.memory offset.toNat 32 =
    word.toByteArray.write 0 right.memory offset.toNat 32
  rw [same]

theorem allocator_memory (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedAllocatorSuccess.returned pre base size tail).memory =
      (pre.toMachineState.mstore (UInt256.ofNat 64)
        (base + NativeSourceCheckedAllocatorFullDecision.amount size)).memory := by
  have after := (NativeSourceCheckedArrayAllocationFrame.exit_frame
    (NativeSourceCheckedAllocatorSuccess.entry pre base size tail)
    (base + NativeSourceCheckedAllocatorFullDecision.amount size) tail).2.2.2
  have before := (NativeSourceCheckedAllocatorFullDecision.frame pre base size (UInt256.ofNat 292 :: tail)).2.1
  exact after.trans (mstore_memory _ _ _ _ before)

theorem original_memory (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedArrayAllocation.returned pre n x array tail).memory =
      (pre.toMachineState.mstore (UInt256.ofNat 64)
        (NativeSourceCheckedArrayAllocation.base pre +
          NativeSourceCheckedAllocatorFullDecision.amount (NativeSourceCheckedArrayAllocation.size n))).memory := by
  have after := allocator_memory (NativeSourceCheckedArrayAllocation.called pre n x array tail)
    (NativeSourceCheckedArrayAllocation.base pre) (NativeSourceCheckedArrayAllocation.size n)
    (NativeSourceCheckedArrayAllocation.rest pre n x array tail)
  have before := (NativeSourceCheckedArrayAllocation.call_frame pre n x array tail).2.2.1
  exact after.trans (mstore_memory _ _ _ _ before)

end Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayMemory
