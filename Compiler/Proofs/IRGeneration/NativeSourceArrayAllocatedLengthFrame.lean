import Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLength

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLengthFrame
open EvmYul EVM EVM.Proof

theorem prefix_frame (pre : EVM.State) (a n x pointer : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 292) :
    (NativeSourceArrayLengthStorePrefix.stored pre a n x pointer tail).pc = UInt256.ofNat 296 ∧
    (NativeSourceArrayLengthStorePrefix.stored pre a n x pointer tail).stack = a :: n :: x :: pointer :: tail ∧
    (NativeSourceArrayLengthStorePrefix.stored pre a n x pointer tail).toState = pre.toState ∧
    (NativeSourceArrayLengthStorePrefix.stored pre a n x pointer tail).memory =
      (pre.toMachineState.mstore pointer n).memory := by
  refine ⟨?_, rfl, rfl, rfl⟩
  change (NativeSourceArrayLengthStorePrefix.s3 pre a n x pointer tail).pc + UInt256.ofNat 1 = _
  rw [(NativeSourceArrayLengthStorePrefix.pcs pre a n x pointer tail pc).2.2]
  decide

theorem original_frame (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :
    (NativeSourceArrayAllocatedLength.stored pre n x array tail).pc = UInt256.ofNat 296 ∧
    (NativeSourceArrayAllocatedLength.stored pre n x array tail).stack =
      array :: n :: x :: NativeSourceCheckedArrayAllocation.base pre :: tail ∧
    (NativeSourceArrayAllocatedLength.stored pre n x array tail).toState = pre.toState := by
  have before := NativeSourceCheckedArrayAllocationFrame.original_frame pre n x array tail
  have after := prefix_frame (NativeSourceArrayAllocatedLength.allocated pre n x array tail)
    array n x (NativeSourceCheckedArrayAllocation.base pre) tail before.1
  exact ⟨after.1, after.2.1, after.2.2.1.trans before.2.2⟩

theorem original_memory (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :
    (NativeSourceArrayAllocatedLength.stored pre n x array tail).memory =
      ((pre.toMachineState.mstore (UInt256.ofNat 64)
        (NativeSourceCheckedArrayAllocation.base pre +
          NativeSourceCheckedAllocatorFullDecision.amount (NativeSourceCheckedArrayAllocation.size n))).mstore
            (NativeSourceCheckedArrayAllocation.base pre) n).memory := by
  have before := NativeSourceCheckedArrayAllocationFrame.original_frame pre n x array tail
  have after := (prefix_frame (NativeSourceArrayAllocatedLength.allocated pre n x array tail)
    array n x (NativeSourceCheckedArrayAllocation.base pre) tail before.1).2.2.2
  have memory := NativeSourceCheckedArrayMemory.original_memory pre n x array tail
  exact after.trans (NativeSourceCheckedArrayMemory.mstore_memory _ _ _ _ memory)

end Compiler.Proofs.IRGeneration.NativeSourceArrayAllocatedLengthFrame
