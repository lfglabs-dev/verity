import Compiler.Proofs.IRGeneration.NativeSourceAllocatorPaddingCopy

namespace Compiler.Proofs.IRGeneration.NativeSourceRequestedGeometry
open EvmYul

theorem difference_toNat (finish base : UInt256) (ordered : base.toNat ≤ finish.toNat) :
    (finish - base).toNat = finish.toNat - base.toNat := by
  change (finish.val - base.val).val = _
  exact Fin.sub_val_of_le ordered

theorem requested_toNat (base length amount gap : UInt256)
    (fits : ((base.toNat + length.toNat) + amount.toNat) + gap.toNat < 2 ^ 256) :
    ((((base + length) + amount) + gap) - base).toNat =
      length.toNat + amount.toNat + gap.toNat := by
  have first := NativeSourceAddressGeometry.add_toNat base length (by omega)
  have second := NativeSourceAddressGeometry.add_toNat (base + length) amount (by omega)
  have third := NativeSourceAddressGeometry.add_toNat ((base + length) + amount) gap (by omega)
  rw [difference_toNat _ base (by omega), third, second, first]
  omega

end Compiler.Proofs.IRGeneration.NativeSourceRequestedGeometry
