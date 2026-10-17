import Compiler.Proofs.IRGeneration.NativeSourceContextSizewordValue

namespace Compiler.Proofs.IRGeneration.NativeSourceSizewordNatural
open EvmYul

theorem mask_value : (UInt256.lnot (UInt256.ofNat 31)).toNat = 2 ^ 256 - 32 := by
  decide

theorem add_value (a b : UInt256) :
    (a + b).toNat = (a.toNat + b.toNat) % (2 ^ 256) := by
  rfl

theorem length_value (finish base : UInt256)
    (ordered : base.toNat + 32 ≤ finish.toNat) :
    ((finish - base) + UInt256.lnot (UInt256.ofNat 31)).toNat =
      finish.toNat - base.toNat - 32 := by
  have difference := NativeSourceRequestedGeometry.difference_toNat finish base (by omega)
  rw [add_value, difference, mask_value]
  have equation : finish.toNat - base.toNat + (2 ^ 256 - 32) =
      (finish.toNat - base.toNat - 32) + 2 ^ 256 := by omega
  rw [equation, Nat.add_mod]
  have bounded : finish.toNat - base.toNat - 32 < 2 ^ 256 := by
    have bound : finish.toNat < 2 ^ 256 := finish.val.isLt
    omega
  rw [Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt bounded]

theorem source_end (finish base : UInt256)
    (ordered : base.toNat + 32 ≤ finish.toNat) :
    base.toNat + 32 + ((finish - base) + UInt256.lnot (UInt256.ofNat 31)).toNat = finish.toNat := by
  rw [length_value finish base ordered]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceSizewordNatural

