import Compiler.Proofs.IRGeneration.NativeSourceStoreActiveGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceCopyActiveExtent
open EvmYul

theorem extent_bound (words dest source count : Nat)
    (upper : words < 2 ^ 251) (destBound : dest < 2 ^ 64)
    (sourceBound : source < 2 ^ 64) (countBound : count < 2 ^ 64) :
    MachineState.M words (max dest source) count < 2 ^ 251 := by
  cases count with
  | zero => exact upper
  | succ n =>
    change max words ((max dest source + (n + 1) + 31) / 32) < _
    apply max_lt upper
    have addressBound : max dest source < 2 ^ 64 := max_lt destBound sourceBound
    omega

theorem copy_bound (machine : MachineState) (dest source count : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (destBound : dest.toNat < 2 ^ 64)
    (sourceBound : source.toNat < 2 ^ 64) (countBound : count.toNat < 2 ^ 64) :
    (machine.mcopy dest source count).activeWords.toNat < 2 ^ 251 := by
  have bound := extent_bound _ _ _ _ upper destBound sourceBound countBound
  change (MachineState.M machine.activeWords.toNat (max dest.toNat source.toNat) count.toNat) % (2 ^ 256) < _
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

theorem extent_monotone (machine : MachineState) (dest source count : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (destBound : dest.toNat < 2 ^ 64)
    (sourceBound : source.toNat < 2 ^ 64) (countBound : count.toNat < 2 ^ 64) :
    machine.activeWords.toNat ≤ (machine.mcopy dest source count).activeWords.toNat := by
  have bound := extent_bound _ _ _ _ upper destBound sourceBound countBound
  change machine.activeWords.toNat ≤ (MachineState.M machine.activeWords.toNat (max dest.toNat source.toNat) count.toNat) % (2 ^ 256)
  rw [Nat.mod_eq_of_lt (by omega)]
  unfold MachineState.M
  split
  · exact Nat.le_refl _
  · exact Nat.le_max_left _ _

theorem guard_preserved (machine : MachineState) (dest source count query : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (destBound : dest.toNat < 2 ^ 64)
    (sourceBound : source.toNat < 2 ^ 64) (countBound : count.toNat < 2 ^ 64)
    (active : ¬query ≥ machine.activeWords * ⟨32⟩) :
    ¬query ≥ (machine.mcopy dest source count).activeWords * ⟨32⟩ := by
  have growth := extent_monotone machine dest source count upper destBound sourceBound countBound
  have afterBound := copy_bound machine dest source count upper destBound sourceBound countBound
  change ¬query.toNat ≥ (machine.activeWords * ⟨32⟩).toNat at active
  change ¬query.toNat ≥ ((machine.mcopy dest source count).activeWords * ⟨32⟩).toNat
  rw [NativeSourceStoreActiveGuard.active_product _ upper] at active
  rw [NativeSourceStoreActiveGuard.active_product _ afterBound]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceCopyActiveExtent

