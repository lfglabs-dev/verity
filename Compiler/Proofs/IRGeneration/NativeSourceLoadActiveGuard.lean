import Compiler.Proofs.IRGeneration.NativeSourceDerivedSecondReturn

namespace Compiler.Proofs.IRGeneration.NativeSourceLoadActiveGuard
open EvmYul

theorem extent_monotone (machine : MachineState) (address : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    machine.activeWords.toNat ≤ (machine.mload address).2.activeWords.toNat := by
  have bound := NativeSourceWordAccessExtent.extent_bound machine.activeWords.toNat address.toNat upper bounded
  change machine.activeWords.toNat ≤ max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32) % (2 ^ 256)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.le_max_left _ _

theorem guard_preserved (machine : MachineState) (address query : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64)
    (active : ¬query ≥ machine.activeWords * ⟨32⟩) :
    ¬query ≥ (machine.mload address).2.activeWords * ⟨32⟩ := by
  have growth := extent_monotone machine address upper bounded
  have afterBound := NativeSourceWordAccessExtent.load_bound machine address upper bounded
  change ¬query.toNat ≥ (machine.activeWords * ⟨32⟩).toNat at active
  change ¬query.toNat ≥ ((machine.mload address).2.activeWords * ⟨32⟩).toNat
  rw [NativeSourceStoreActiveGuard.active_product _ upper] at active
  rw [NativeSourceStoreActiveGuard.active_product _ afterBound]
  omega

theorem loaded_guard (machine : MachineState) (address : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    ¬address ≥ (machine.mload address).2.activeWords * ⟨32⟩ := by
  have bound := NativeSourceWordAccessExtent.load_bound machine address upper bounded
  change ¬address.toNat ≥ ((machine.mload address).2.activeWords * ⟨32⟩).toNat
  rw [NativeSourceStoreActiveGuard.active_product _ bound]
  have extentBound := NativeSourceWordAccessExtent.extent_bound machine.activeWords.toNat address.toNat upper bounded
  have value : (machine.mload address).2.activeWords.toNat =
      max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32) := by
    change max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32) % (2 ^ 256) = _
    exact Nat.mod_eq_of_lt (by omega)
  rw [value]
  have larger := Nat.le_max_right machine.activeWords.toNat ((address.toNat + 32 + 31) / 32)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceLoadActiveGuard
