import Compiler.Proofs.IRGeneration.NativeSourceContextAllocatedBytes

namespace Compiler.Proofs.IRGeneration.NativeSourceLengthwordGeometry
open EvmYul

theorem sub_toNat (finish base : UInt256) (ordered : base.toNat ≤ finish.toNat) :
    (finish - base).toNat = finish.toNat - base.toNat := by
  exact Fin.sub_val_of_le ordered

theorem add_mod (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % (2 ^ 256) := by
  rfl

theorem length_toNat (finish base : UInt256) (ordered : base.toNat + 32 ≤ finish.toNat) :
    ((finish - base) + UInt256.lnot (UInt256.ofNat 31)).toNat = finish.toNat - base.toNat - 32 := by
  have subValue := sub_toNat finish base (by omega)
  have mask : (UInt256.lnot (UInt256.ofNat 31)).toNat = 2 ^ 256 - 32 := by
    change ((UInt256.ofNat (2 ^ 256 - 1)) - UInt256.ofNat 31).toNat = _
    rw [sub_toNat _ _ (by decide)]
    change ((2 ^ 256 - 1) % (2 ^ 256)) - (31 % (2 ^ 256)) = _
    norm_num
  rw [add_mod, subValue, mask]
  have bound := finish.val.isLt
  change finish.toNat < 2 ^ 256 at bound
  have rearrange : finish.toNat - base.toNat + (2 ^ 256 - 32) = (finish.toNat - base.toNat - 32) + 2 ^ 256 := by omega
  rw [rearrange, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem source_endpoint (finish base source : UInt256)
    (ordered : base.toNat + 32 ≤ finish.toNat)
    (sourceValue : source.toNat = base.toNat + 32) :
    source.toNat + ((finish - base) + UInt256.lnot (UInt256.ofNat 31)).toNat = finish.toNat := by
  rw [length_toNat finish base ordered, sourceValue]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceLengthwordGeometry
