import Compiler.Proofs.IRGeneration.NativeSourceBoundedPadding

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorAcceptedBounds
open EvmYul NativeSourceAllocatorOverflowEntry

theorem comparisons (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    ¬base + amount size > UInt256.ofNat (2 ^ 64 - 1) ∧ ¬base + amount size < base := by
  unfold NativeSourceAllocatorDecision.flag UInt256.gt UInt256.lt UInt256.fromBool at guard
  by_cases limit : base + amount size > UInt256.ofNat (2 ^ 64 - 1)
  · by_cases overflow : base + amount size < base
    · simp only [limit, overflow] at guard
      exact False.elim ((by decide : UInt256.lor true.toUInt256 true.toUInt256 ≠ ⟨0⟩) guard)
    · simp only [limit, overflow] at guard
      exact False.elim ((by decide : UInt256.lor true.toUInt256 false.toUInt256 ≠ ⟨0⟩) guard)
  · by_cases overflow : base + amount size < base
    · simp only [limit, overflow] at guard
      exact False.elim ((by decide : UInt256.lor false.toUInt256 true.toUInt256 ≠ ⟨0⟩) guard)
    · exact ⟨limit, overflow⟩

theorem natural_bounds (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    (base + amount size).toNat < 2 ^ 64 ∧ base.toNat ≤ (base + amount size).toNat := by
  have bounds := comparisons base size guard
  change ¬(base + amount size).toNat > (UInt256.ofNat (2 ^ 64 - 1)).toNat ∧
    ¬(base + amount size).toNat < base.toNat at bounds
  have maximum : (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide
  rw [maximum] at bounds
  omega

theorem sum_bound (base size : UInt256)
    (guard : NativeSourceAllocatorDecision.flag base size = ⟨0⟩) :
    base.toNat + (amount size).toNat < 2 ^ 64 := by
  have bounds := natural_bounds base size guard
  have baseFits : base.toNat < 2 ^ 256 := base.val.isLt
  have amountFits : (amount size).toNat < 2 ^ 256 := (amount size).val.isLt
  have monotone := bounds.2
  change base.toNat ≤ (base.toNat + (amount size).toNat) % (2 ^ 256) at monotone
  have noWrap : base.toNat + (amount size).toNat < 2 ^ 256 := by omega
  rw [NativeSourceAddressGeometry.add_toNat base (amount size) noWrap] at bounds
  exact bounds.1

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorAcceptedBounds

