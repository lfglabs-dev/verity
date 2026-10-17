import Compiler.Proofs.IRGeneration.NativeSourceContextFree

namespace Compiler.Proofs.IRGeneration.NativeSourcePointerExtent
open EvmYul

theorem active_guard (words : UInt256) (lower : 3 ≤ words.toNat)
    (upper : words.toNat < 2 ^ 251) :
    ¬UInt256.ofNat 64 ≥ words * ⟨32⟩ := by
  have fits : words.toNat * 32 < 2 ^ 256 := by omega
  have product : (words * ⟨32⟩).toNat = words.toNat * 32 := by
    change (words.toNat * 32) % (2 ^ 256) = _
    exact Nat.mod_eq_of_lt fits
  change ¬64 ≥ (words * ⟨32⟩).toNat
  rw [product]
  omega

theorem context_free (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (padding : 64 - (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).memory.size <
      2 ^ System.Platform.numBits)
    (upper : (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords.toNat <
      2 ^ 251) :
    NativeSourceDecodedPackingStart.free cost
      (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail) =
      j + NativeSourceAllocatorOverflowEntry.amount (b - c) := by
  apply NativeSourceContextFree.context_free cost pre a b c d e f g h i j k tail padding
  exact active_guard _
    (NativeSourcePointerActive.context_allocated cost pre a b c d e f g h i j k tail) upper

end Compiler.Proofs.IRGeneration.NativeSourcePointerExtent

