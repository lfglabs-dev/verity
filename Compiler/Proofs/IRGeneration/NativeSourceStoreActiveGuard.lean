import Compiler.Proofs.IRGeneration.NativeSourceLookupFrame

namespace Compiler.Proofs.IRGeneration.NativeSourceStoreActiveGuard
open EvmYul

theorem extent_monotone (machine : MachineState) (address value : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    machine.activeWords.toNat ≤ (machine.mstore address value).activeWords.toNat := by
  have bound := NativeSourceWordAccessExtent.extent_bound machine.activeWords.toNat address.toNat upper bounded
  change machine.activeWords.toNat ≤ max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32) % (2 ^ 256)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.le_max_left _ _

theorem active_product (words : UInt256) (upper : words.toNat < 2 ^ 251) :
    (words * ⟨32⟩).toNat = words.toNat * 32 := by
  change (words.toNat * 32) % (2 ^ 256) = _
  exact Nat.mod_eq_of_lt (by omega)

theorem guard_preserved (machine : MachineState) (address value query : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64)
    (active : ¬query ≥ machine.activeWords * ⟨32⟩) :
    ¬query ≥ (machine.mstore address value).activeWords * ⟨32⟩ := by
  have growth := extent_monotone machine address value upper bounded
  have afterBound := NativeSourceWordAccessExtent.store_bound machine address value upper bounded
  change ¬query.toNat ≥ (machine.activeWords * ⟨32⟩).toNat at active
  change ¬query.toNat ≥ ((machine.mstore address value).activeWords * ⟨32⟩).toNat
  rw [active_product _ upper] at active
  rw [active_product _ afterBound]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceStoreActiveGuard
