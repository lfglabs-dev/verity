import Compiler.Proofs.IRGeneration.NativeSourceSizeActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorActiveGuard
open EvmYul

theorem context_guard (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k query : UInt256)
    (tail : Stack UInt256)
    (upper : (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (active : ¬query ≥ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩) :
    ¬query ≥ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩ := by
  have afterBound := NativeSourceAllocatorExtent.context_bound cost pre a b c d e f g h i j k tail upper
  change ¬query.toNat ≥ ((NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩).toNat at active
  change ¬query.toNat ≥ ((NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩).toNat
  rw [NativeSourceStoreActiveGuard.active_product _ upper] at active
  rw [NativeSourceStoreActiveGuard.active_product _ afterBound, NativeSourceAllocatorExtent.context_words]
  have growth := Nat.le_max_left (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords.toNat 3
  omega

theorem sizeword_guard (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (upper : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (address : j.toNat < 2 ^ 64) :
    ¬j ≥ (NativeSourceFieldsAllocation.returned cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩ := by
  exact context_guard cost pre a b c d e f g h i j k j tail
    (NativeSourceSizeFieldExtent.context_bound cost pre a b c d e f g h i j k tail upper address)
    (NativeSourceSizeActiveGuard.context_guard cost pre a b c d e f g h i j k tail upper address)

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorActiveGuard
