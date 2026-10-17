import Compiler.Proofs.IRGeneration.NativeSourcePointerLookup
namespace Compiler.Proofs.IRGeneration.NativeSourceContextFree
open EvmYul

theorem free_lookup (cost : Nat) (pre : EVM.State) :
    NativeSourceDecodedPackingStart.free cost pre =
      pre.toMachineState.lookupMemory (UInt256.ofNat 64) := by
  rfl

theorem context_free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits)
    (active : ¬UInt256.ofNat 64 ≥
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩) :
    NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail) =
      j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  rw [free_lookup]
  exact NativeSourcePointerLookup.context_lookup cost pre a b c d e f g h i j k tail padding active

end Compiler.Proofs.IRGeneration.NativeSourceContextFree
