import Compiler.Proofs.IRGeneration.NativeSourceArrayElementGuard

namespace Compiler.Proofs.IRGeneration.NativeSourceArrayElementBounds
open EvmYul EVM EVM.Proof NativeSourceArrayElementGuard

theorem signed_not_less (left right : UInt256)
    (left_nonnegative : left.toNat < 2^255) (right_nonnegative : right.toNat < 2^255)
    (ordered : right.toNat ≤ left.toNat) : UInt256.slt left right = UInt256.ofNat 0 := by
  unfold UInt256.slt UInt256.sltBool
  rw [if_neg (by omega), if_neg (by omega)]
  have compared : (decide (left < right)) = false := by
    apply decide_eq_false
    change ¬left.val < right.val
    change ¬left.toNat < right.toNat
    omega
  rw [compared]
  rfl

theorem remaining (pre : EVM.State) (cursor : UInt256)
    (small : pre.executionEnv.calldata.size < 2^255)
    (inside : cursor.toNat ≤ pre.executionEnv.calldata.size) :
    (size pre - cursor).toNat = pre.executionEnv.calldata.size - cursor.toNat := by
  have exactSize : (size pre).toNat = pre.executionEnv.calldata.size := by
    change pre.executionEnv.calldata.size % UInt256.size = _
    have modulus : 2^255 < UInt256.size := by decide
    exact Nat.mod_eq_of_lt (by omega)
  have subValue : (size pre - cursor).toNat = (size pre).toNat - cursor.toNat :=
    Fin.sub_val_of_le (by change cursor.toNat ≤ (size pre).toNat; omega)
  omega

theorem flag_zero (pre : EVM.State) (cursor : UInt256)
    (small : pre.executionEnv.calldata.size < 2^255)
    (room : cursor.toNat + 128 ≤ pre.executionEnv.calldata.size) :
    flag pre cursor = UInt256.ofNat 0 := by
  have exactRemaining := remaining pre cursor small (by omega)
  exact signed_not_less _ _ (by omega) (by decide) (by change 128 ≤ (size pre - cursor).toNat; omega)

theorem accepted_pc (pre : EVM.State) (a end_ cursor : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 806) (small : pre.executionEnv.calldata.size < 2^255)
    (room : cursor.toNat + 128 ≤ pre.executionEnv.calldata.size) :
    (decided pre a end_ cursor tail).pc = UInt256.ofNat 817 := by
  change (NativeSourceArrayElementBranch.branched (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail)).pc = _
  rw [NativeSourceArrayElementBranch.destinations (s7 pre a end_ cursor tail) (flag pre cursor)
    (a :: end_ :: cursor :: tail) (pcs pre a end_ cursor tail pc).2.2.2.2.2.2,
    flag_zero pre cursor small room]
  rfl

theorem canonical_room (pre : EVM.State) (selector key value : Nat)
    (market : NativeSourceMarketCalldata.Market) (index : Nat)
    (encoded : pre.executionEnv.calldata = Compiler.Proofs.YulGeneration.Backends.StateBridge.calldataToByteArray selector
      (NativeSourceMarketCalldata.arguments market key value))
    (inside : index < market.collateral.length) (small : pre.executionEnv.calldata.size < 2^255) :
    (NativeSourceMarketArrayCursor.cursor index).toNat + 128 ≤ pre.executionEnv.calldata.size := by
  have total := NativeSourceMarketArrayBounds.calldata_size pre selector key value market encoded
  have modulus : 2^255 < UInt256.size := by decide
  have position := NativeSourceMarketArrayCursor.cursor_value index market.collateral.length (by omega) (by omega)
  omega

end Compiler.Proofs.IRGeneration.NativeSourceArrayElementBounds
