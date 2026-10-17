import Compiler.Proofs.IRGeneration.NativeSourceWordRoundtrip

namespace Compiler.Proofs.IRGeneration.NativeSourcePointerLookup
open EvmYul

theorem allocator_carrier (cost : Nat) (pre : EVM.State) (pointer target : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - pre.memory.size < 2 ^ System.Platform.numBits) :
    64 < (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory.size := by
  have extent := MachineState.le_size_memory_mstore
    (EVM.Proof.stepPre cost (NativeSourceAllocatorReturn.pushed cost pre)).toMachineState
    (UInt256.ofNat 64) pointer padding
  change 64 + 32 ≤ (NativeSourceAllocatorReturn.returned cost pre pointer target tail).memory.size at extent
  omega

theorem allocator_lookup (cost : Nat) (pre : EVM.State) (pointer target : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - pre.memory.size < 2 ^ System.Platform.numBits)
    (active : ¬UInt256.ofNat 64 ≥
      (NativeSourceAllocatorReturn.returned cost pre pointer target tail).activeWords * ⟨32⟩) :
    (NativeSourceAllocatorReturn.returned cost pre pointer target tail).toMachineState.lookupMemory
      (UInt256.ofNat 64) = pointer := by
  apply NativeSourceWordRoundtrip.lookup_of_bytes
  · exact allocator_carrier cost pre pointer target tail padding
  · exact active
  · exact NativeSourcePointerBytes.allocator_pointer cost pre pointer target tail padding


theorem context_lookup (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits)
    (active : ¬UInt256.ofNat 64 ≥
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩) :
    (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).toMachineState.lookupMemory
      (UInt256.ofNat 64) = j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  apply allocator_lookup
  · rw [NativeSourceAllocatorPrefixMemory.decided, NativeSourceFirstAllocatorFrame.entered_memory]
    exact padding
  · exact active

end Compiler.Proofs.IRGeneration.NativeSourcePointerLookup


