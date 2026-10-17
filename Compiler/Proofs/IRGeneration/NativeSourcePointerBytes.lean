import Compiler.Proofs.IRGeneration.NativeSourceRequestedMargin

namespace Compiler.Proofs.IRGeneration.NativeSourcePointerBytes
open EvmYul

theorem stored_word (machine : MachineState) (address value : UInt256)
    (padding : address.toNat - machine.memory.size < 2 ^ System.Platform.numBits) :
    (machine.mstore address value).memory.readWithPadding address.toNat 32 = value.toByteArray := by
  change (ByteArray.write value.toByteArray 0 machine.memory address.toNat 32).readWithPadding address.toNat 32 = _
  exact ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by decide) (by decide)
    (UInt256.size_toByteArray value) padding

theorem allocator_pointer (cost : Nat) (pre : EVM.State) (pointer target : UInt256) (tail : Stack UInt256)
    (padding : 64 - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory.readWithPadding 64 32 = pointer.toByteArray := by
  exact stored_word (EVM.Proof.stepPre cost (NativeSourceAllocatorReturn.pushed cost pre)).toMachineState
    (UInt256.ofNat 64) pointer padding

theorem success_pointer (cost : Nat) (pre : EVM.State) (base size target : UInt256) (tail : Stack UInt256)
    (padding : 64 - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceAllocatorSuccess.returned cost pre base size target tail).memory.readWithPadding 64 32 =
      (base + NativeSourceAllocatorOverflowEntry.amount size).toByteArray := by
  unfold NativeSourceAllocatorSuccess.returned
  apply allocator_pointer
  rw [NativeSourceAllocatorPrefixMemory.decided]
  exact padding

theorem caller_pointer (cost : Nat) (pre : EVM.State) (size target a b c d base : UInt256) (tail : Stack UInt256)
    (padding : 64 - pre.memory.size < 2 ^ System.Platform.numBits) :
    (NativeSourceFirstAllocatorCaller.returned cost pre size target a b c d base tail).memory.readWithPadding 64 32 =
      (base + NativeSourceAllocatorOverflowEntry.amount size).toByteArray := by
  unfold NativeSourceFirstAllocatorCaller.returned
  apply success_pointer
  rw [NativeSourceFirstAllocatorFrame.entered_memory]
  exact padding

theorem context_pointer (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256) (tail : Stack UInt256)
    (padding : 64 - (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).memory.readWithPadding 64 32 =
      (j + NativeSourceAllocatorOverflowEntry.amount (b - c)).toByteArray := by
  exact caller_pointer cost _ (b - c) (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j (k :: UInt256.ofNat 0 :: tail) padding

end Compiler.Proofs.IRGeneration.NativeSourcePointerBytes

