import Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorSuccess

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBounds
open EvmYul EVM EVM.Proof

theorem flag_zero (base pointer : UInt256)
    (nonwrap : base.toNat ≤ pointer.toNat) (limit : pointer.toNat ≤ 2^64-1) :
    NativeSourceCheckedAllocatorDecision.condition (UInt256.lt pointer base) pointer = UInt256.ofNat 0 := by
  have noOverflow : ¬pointer < base := by
    change ¬pointer.val < base.val
    change ¬pointer.toNat < base.toNat
    omega
  have noLimit : ¬pointer > UInt256.ofNat (2^64-1) := by
    change ¬pointer.val > (UInt256.ofNat (2^64-1)).val
    change ¬pointer.toNat > (UInt256.ofNat (2^64-1)).toNat
    have exactLimit : (UInt256.ofNat (2^64-1)).toNat = 2^64-1 := by decide
    omega
  simp only [NativeSourceCheckedAllocatorDecision.condition, UInt256.gt, UInt256.lt,
    UInt256.fromBool, noOverflow, noLimit, decide_false]
  rfl

theorem addition (base amount : UInt256) (bound : base.toNat + amount.toNat < UInt256.size) :
    (base + amount).toNat = base.toNat + amount.toNat := by
  change (base.toNat + amount.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt bound

theorem accepted (base size : UInt256)
    (bound : base.toNat + (NativeSourceCheckedAllocatorFullDecision.amount size).toNat ≤ 2^64-1) :
    (NativeSourceCheckedAllocatorFullDecision.condition base size != ⟨0⟩) = false := by
  have small : base.toNat + (NativeSourceCheckedAllocatorFullDecision.amount size).toNat < UInt256.size := by
    have : 2^64-1 < UInt256.size := by decide
    omega
  have sum := addition base (NativeSourceCheckedAllocatorFullDecision.amount size) small
  have zero := flag_zero base (base + NativeSourceCheckedAllocatorFullDecision.amount size) (by omega) (by omega)
  change NativeSourceCheckedAllocatorFullDecision.condition base size = UInt256.ofNat 0 at zero
  rw [zero]
  rfl

end Compiler.Proofs.IRGeneration.NativeSourceCheckedAllocatorBounds
