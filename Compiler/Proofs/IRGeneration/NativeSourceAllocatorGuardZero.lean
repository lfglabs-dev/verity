import Compiler.Proofs.IRGeneration.NativeSourceAllocatorSuccess

namespace Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuardZero
open EvmYul NativeSourceAllocatorOverflowEntry

theorem flag_zero (base size : UInt256)
    (limit : ¬base + amount size > UInt256.ofNat (2^64-1))
    (overflow : ¬base + amount size < base) :
    NativeSourceAllocatorDecision.flag base size = ⟨0⟩ := by
  unfold NativeSourceAllocatorDecision.flag UInt256.gt UInt256.lt UInt256.fromBool
  simp only [limit, overflow]
  decide

theorem flag_zero_nat (base size : UInt256)
    (limit : (base + amount size).toNat ≤ 2^64-1)
    (overflow : base.toNat ≤ (base + amount size).toNat) :
    NativeSourceAllocatorDecision.flag base size = ⟨0⟩ := by
  apply flag_zero base size
  · change ¬(base + amount size).toNat > (UInt256.ofNat (2^64-1)).toNat
    have maximum : (UInt256.ofNat (2^64-1)).toNat = 2^64-1 := by decide
    rw [maximum]
    omega
  · change ¬(base + amount size).toNat < base.toNat
    omega

end Compiler.Proofs.IRGeneration.NativeSourceAllocatorGuardZero
