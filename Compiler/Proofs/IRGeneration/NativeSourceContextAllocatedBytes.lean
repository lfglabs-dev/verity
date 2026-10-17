import Compiler.Proofs.IRGeneration.NativeSourceContextSizedBytes
import Compiler.Proofs.IRGeneration.NativeSourceFirstAllocatorFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceContextAllocatedBytes
open EvmYul

theorem returned_memory (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory =
      pointer.toByteArray.write 0 pre.memory 64 32 := by
  rfl

theorem success_memory (cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256) :
    (NativeSourceAllocatorSuccess.returned cost pre base size target tail).memory =
      (base + NativeSourceAllocatorOverflowEntry.amount size).toByteArray.write 0 pre.memory 64 32 := by
  unfold NativeSourceAllocatorSuccess.returned
  rw [returned_memory, NativeSourceAllocatorPrefixMemory.decided]

theorem caller_memory (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256) (tail : Stack UInt256) :
    (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).memory =
      (base + NativeSourceAllocatorOverflowEntry.amount size).toByteArray.write 0 pre.memory 64 32 := by
  unfold NativeSourceFirstAllocatorCaller.returned
  rw [success_memory, NativeSourceFirstAllocatorFrame.entered_memory]

theorem context_memory (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory =
      (j + NativeSourceAllocatorOverflowEntry.amount (b - c)).toByteArray.write 0
        (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory 64 32 := by
  unfold NativeSourceFieldsAllocation.returned
  rw [caller_memory]

theorem encoded_context (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory =
      (j + NativeSourceAllocatorOverflowEntry.amount (b - c)).toByteArray.write 0
        (((b - c) + UInt256.lnot (UInt256.ofNat 31)).toByteArray.write 0
        ((((NativeSourceThirdField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory g).land a).toByteArray.write 0
          ((((NativeSourceSecondField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory f).land a).toByteArray.write 0
            (((NativeSourceFirstField.stored cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory e).toByteArray.write 0
              (((NativeSourcePackingContext.prepared cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory d).toByteArray.write 0
                pre.memory (c + UInt256.ofNat 192).toNat 32)
              (c + UInt256.ofNat 224).toNat 32)
            (c + UInt256.ofNat 256).toNat 32)
          (c + UInt256.ofNat 288).toNat 32)
        j.toNat 32) 64 32 := by
  rw [context_memory, NativeSourceContextSizedBytes.encoded_memory]

end Compiler.Proofs.IRGeneration.NativeSourceContextAllocatedBytes
