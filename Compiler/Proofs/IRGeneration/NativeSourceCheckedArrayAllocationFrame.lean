import Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocation

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocationFrame
open EvmYul EVM EVM.Proof

theorem exit_frame (pre : EVM.State) (pointer : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedAllocatorExit.returned pre pointer tail).pc = UInt256.ofNat 292 ∧
    (NativeSourceCheckedAllocatorExit.returned pre pointer tail).stack = tail ∧
    (NativeSourceCheckedAllocatorExit.returned pre pointer tail).toState = pre.toState ∧
    (NativeSourceCheckedAllocatorExit.returned pre pointer tail).memory =
      (pre.toMachineState.mstore (UInt256.ofNat 64) pointer).memory := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem allocator_frame (pre : EVM.State) (base size : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedAllocatorSuccess.returned pre base size tail).pc = UInt256.ofNat 292 ∧
    (NativeSourceCheckedAllocatorSuccess.returned pre base size tail).stack = tail ∧
    (NativeSourceCheckedAllocatorSuccess.returned pre base size tail).toState = pre.toState := by
  have atExit := exit_frame (NativeSourceCheckedAllocatorSuccess.entry pre base size tail)
    (base + NativeSourceCheckedAllocatorFullDecision.amount size) tail
  have before := NativeSourceCheckedAllocatorFullDecision.frame pre base size (UInt256.ofNat 292 :: tail)
  exact ⟨atExit.1, atExit.2.1, atExit.2.2.1.trans before.2.2⟩

theorem original_frame (pre : EVM.State) (n x array : UInt256) (tail : Stack UInt256) :
    (NativeSourceCheckedArrayAllocation.returned pre n x array tail).pc = UInt256.ofNat 292 ∧
    (NativeSourceCheckedArrayAllocation.returned pre n x array tail).stack =
      NativeSourceCheckedArrayAllocation.rest pre n x array tail ∧
    (NativeSourceCheckedArrayAllocation.returned pre n x array tail).toState = pre.toState := by
  have after := allocator_frame (NativeSourceCheckedArrayAllocation.called pre n x array tail)
    (NativeSourceCheckedArrayAllocation.base pre) (NativeSourceCheckedArrayAllocation.size n)
    (NativeSourceCheckedArrayAllocation.rest pre n x array tail)
  have before := NativeSourceCheckedArrayAllocation.call_frame pre n x array tail
  exact ⟨after.1, after.2.1, after.2.2.trans before.2.2.2⟩

end Compiler.Proofs.IRGeneration.NativeSourceCheckedArrayAllocationFrame
