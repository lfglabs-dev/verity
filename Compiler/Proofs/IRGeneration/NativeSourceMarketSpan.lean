import Compiler.Proofs.IRGeneration.NativeSourceSpanBounds

namespace Compiler.Proofs.IRGeneration.NativeSourceMarketSpan
open EvmYul EVM EVM.Proof NativeSourceMarketCalldata
open Compiler.Proofs.YulGeneration.Backends

theorem encoded_size (pre : EVM.State) (selector key value : Nat) (m : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value)) :
    pre.executionEnv.calldata.size = 388 + 128 * m.collateral.length := by
  rw [encoded, StateBridge.calldataToByteArray_size]
  simp only [arguments, List.length_append, List.length_cons, List.length_nil, collateral_length]
  omega

theorem market_flag_zero (pre : EVM.State) (selector key value : Nat) (m : Market)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (bounded : 388 + 128 * m.collateral.length < 2^255) :
    NativeSourceCollateralSpan.flag pre (UInt256.ofNat 96) (UInt256.ofNat 256) = UInt256.ofNat 0 := by
  have size := encoded_size pre selector key value m encoded
  apply NativeSourceSpanBounds.canonical_flag_zero
  · omega
  · omega

theorem market_accept (fuel : Nat) (pre : EVM.State) (x y base : UInt256) (tail : Stack UInt256)
    (selector key value : Nat) (m : Market)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = UInt256.ofNat 256 :: x :: y :: UInt256.ofNat 96 :: base :: tail)
    (encoded : pre.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (bounded : 388 + 128 * m.collateral.length < 2^255)
    (gas : 39 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 12) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough
          (NativeSourceCollateralSpan.s10 pre (UInt256.ofNat 256) x y (UInt256.ofNat 96) base tail)
          (x :: NativeSourceCollateralSpan.array (UInt256.ofNat 96) (UInt256.ofNat 256) :: y :: UInt256.ofNat 96 :: base :: tail)) := by
  exact NativeSourceSpanBranches.accept fuel pre _ x y _ base tail code pc stack
    (market_flag_zero pre selector key value m encoded bounded) gas depth

theorem accepted_frame (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (pc : pre.pc = UInt256.ofNat 239) :
    (NativeSourceCheckedReturn.fallthrough (NativeSourceCollateralSpan.s10 pre offset x y a base tail)
      (x :: NativeSourceCollateralSpan.array a offset :: y :: a :: base :: tail)).pc = UInt256.ofNat 253 ∧
    (NativeSourceCheckedReturn.fallthrough (NativeSourceCollateralSpan.s10 pre offset x y a base tail)
      (x :: NativeSourceCollateralSpan.array a offset :: y :: a :: base :: tail)).toState = pre.toState ∧
    (NativeSourceCheckedReturn.fallthrough (NativeSourceCollateralSpan.s10 pre offset x y a base tail)
      (x :: NativeSourceCollateralSpan.array a offset :: y :: a :: base :: tail)).memory = pre.memory := by
  refine ⟨?_, rfl, rfl⟩
  change (NativeSourceCollateralSpan.s10 pre offset x y a base tail).pc + UInt256.ofNat 1 = _
  rw [NativeSourceCollateralSpan.output_pc pre offset x y a base tail pc]
  decide

end Compiler.Proofs.IRGeneration.NativeSourceMarketSpan
