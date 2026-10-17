import Compiler.Proofs.IRGeneration.NativeSourcePreallocatorFree

namespace Compiler.Proofs.IRGeneration.NativeSourceWordAccessExtent
open EvmYul

theorem extent_bound (words address : Nat)
    (upper : words < 2 ^ 251) (bounded : address < 2 ^ 64) :
    max words ((address + 32 + 31) / 32) < 2 ^ 251 := by
  apply max_lt upper
  omega

theorem store_bound (machine : MachineState) (address value : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    (machine.mstore address value).activeWords.toNat < 2 ^ 251 := by
  have bound := extent_bound machine.activeWords.toNat address.toNat upper bounded
  change (max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32)) % (2 ^ 256) < _
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

theorem load_bound (machine : MachineState) (address : UInt256)
    (upper : machine.activeWords.toNat < 2 ^ 251) (bounded : address.toNat < 2 ^ 64) :
    (machine.mload address).2.activeWords.toNat < 2 ^ 251 := by
  have bound := extent_bound machine.activeWords.toNat address.toNat upper bounded
  change (max machine.activeWords.toNat ((address.toNat + 32 + 31) / 32)) % (2 ^ 256) < _
  rw [Nat.mod_eq_of_lt (by omega)]
  exact bound

end Compiler.Proofs.IRGeneration.NativeSourceWordAccessExtent
