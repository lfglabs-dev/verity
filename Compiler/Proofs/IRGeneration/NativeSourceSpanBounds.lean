import Compiler.Proofs.IRGeneration.NativeSourceSpanBranches

namespace Compiler.Proofs.IRGeneration.NativeSourceSpanBounds
open EvmYul EVM EVM.Proof NativeSourceCollateralSpan

theorem signed_less (left right : UInt256)
    (left_nonnegative : left.toNat < 2^255) (right_nonnegative : right.toNat < 2^255)
    (less : left.toNat < right.toNat) : UInt256.slt left right = UInt256.ofNat 1 := by
  unfold UInt256.slt UInt256.sltBool
  rw [if_neg (by omega), if_neg (by omega)]
  have compared : (decide (left < right)) = true := by
    apply decide_eq_true
    change left.val < right.val
    exact less
  rw [compared]
  rfl

theorem flag_zero (pre : EVM.State) (a offset : UInt256)
    (left_nonnegative : (array a offset + UInt256.ofNat 35).toNat < 2^255)
    (right_nonnegative : (size pre).toNat < 2^255)
    (span : (array a offset + UInt256.ofNat 35).toNat < (size pre).toNat) :
    flag pre a offset = UInt256.ofNat 0 := by
  unfold flag
  rw [signed_less _ _ left_nonnegative right_nonnegative span]
  decide

theorem canonical_flag_zero (pre : EVM.State)
    (minimum : 388 ≤ pre.executionEnv.calldata.size)
    (maximum : pre.executionEnv.calldata.size < 2^255) :
    flag pre (UInt256.ofNat 96) (UInt256.ofNat 256) = UInt256.ofNat 0 := by
  have sized : (size pre).toNat = pre.executionEnv.calldata.size := by
    change pre.executionEnv.calldata.size % UInt256.size = pre.executionEnv.calldata.size
    apply Nat.mod_eq_of_lt
    have modulus : 2^255 < UInt256.size := by decide
    omega
  have left : (array (UInt256.ofNat 96) (UInt256.ofNat 256) + UInt256.ofNat 35).toNat = 387 := by decide
  apply flag_zero
  · rw [left]; decide
  · rw [sized]; exact maximum
  · rw [left, sized]; omega

end Compiler.Proofs.IRGeneration.NativeSourceSpanBounds
