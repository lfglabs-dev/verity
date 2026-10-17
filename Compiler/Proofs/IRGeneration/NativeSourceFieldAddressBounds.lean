import Compiler.Proofs.IRGeneration.NativeSourceOriginalFree

namespace Compiler.Proofs.IRGeneration.NativeSourceFieldAddressBounds
open EvmYul

theorem offset_bound (base : UInt256) (offset : Nat) (small : offset < 2 ^ 256)
    (bound : base.toNat + offset < 2 ^ 64) :
    (base + UInt256.ofNat offset).toNat < 2 ^ 64 := by
  rw [NativeSourceFieldGeometry.offset_toNat base offset small (by omega)]
  exact bound

theorem field_bounds (base : UInt256) (bound : base.toNat + 288 < 2 ^ 64) :
    (base + UInt256.ofNat 192).toNat < 2 ^ 64 ∧
    (base + UInt256.ofNat 224).toNat < 2 ^ 64 ∧
    (base + UInt256.ofNat 256).toNat < 2 ^ 64 ∧
    (base + UInt256.ofNat 288).toNat < 2 ^ 64 := by
  exact ⟨offset_bound base 192 (by decide) (by omega),
    offset_bound base 224 (by decide) (by omega),
    offset_bound base 256 (by decide) (by omega),
    offset_bound base 288 (by decide) bound⟩

end Compiler.Proofs.IRGeneration.NativeSourceFieldAddressBounds
