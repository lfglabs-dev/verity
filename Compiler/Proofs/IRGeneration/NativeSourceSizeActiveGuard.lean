import Compiler.Proofs.IRGeneration.NativeSourceLoadActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceSizeActiveGuard
open EvmYul

theorem store_load_extent (machine : MachineState) (address value : UInt256) :
    (machine.mstore address value).activeWords = (machine.mload address).2.activeWords := by
  rfl

theorem stored_guard (machine : MachineState) (address value : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    ¬address ≥ (machine.mstore address value).activeWords * ⟨32⟩ := by
  rw [store_load_extent]
  exact NativeSourceLoadActiveGuard.loaded_guard machine address upper bounded

theorem sized_guard (cost : Nat) (pre : EVM.State) (a b c d e f g h i : UInt256)
    (tail : Stack UInt256) (upper : pre.activeWords.toNat < 2 ^ 251) (address : h.toNat < 2 ^ 64) :
    ¬h ≥ (NativeSourceFieldSize.stored cost pre a b c d e f g h i tail).activeWords * ⟨32⟩ := by
  rw [NativeSourceSizeFieldExtent.sized_words]
  exact NativeSourceLoadActiveGuard.loaded_guard pre.toMachineState h upper address

theorem context_guard (cost : Nat) (pre : EVM.State) (a b c d e f g h i j k : UInt256)
    (tail : Stack UInt256)
    (upper : (NativeSourceFourthField.stored cost pre a b c d e f g h i j k tail).activeWords.toNat < 2 ^ 251)
    (address : j.toNat < 2 ^ 64) :
    ¬j ≥ (NativeSourceSizedFields.stored cost pre a b c d e f g h i j k tail).activeWords * ⟨32⟩ := by
  exact sized_guard cost _ b c (UInt256.ofNat 632) h (UInt256.ofNat 32) i
    (UInt256.ofNat 681) j k (UInt256.ofNat 0 :: tail) upper address

end Compiler.Proofs.IRGeneration.NativeSourceSizeActiveGuard
