import Compiler.Proofs.IRGeneration.NativeSourceCheckedSpan

namespace Compiler.Proofs.IRGeneration.NativeSourceSpanBranches
open EvmYul EVM EVM.Proof NativeSourceCollateralSpan

theorem zero_jump (fuel : Nat) (pre : EVM.State) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 252)
    (stack : pre.stack = UInt256.ofNat 91 :: UInt256.ofNat 0 :: tail)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, decode252]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre (UInt256.ofNat 0) tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (NativeSourceCheckedReturn.zero_transition fuel pre tail stack) rfl

theorem nonzero_jump (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 252)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedJumpRejection.afterJump pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, decode252]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre condition tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (NativeSourceCheckedJumpRejection.transition fuel pre condition tail stack nonzero) rfl

theorem accept (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (valid : flag pre a offset = UInt256.ofNat 0)
    (gas : 39 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 12) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0))
        (NativeSourceCheckedReturn.fallthrough (s10 pre offset x y a base tail) (x :: array a offset :: y :: a :: base :: tail)) := by
  have charged := prefix_gas pre offset x y a base tail (by omega)
  rw [NativeSourceCheckedSpan.execute_prefix (fuel + 1) _ pre offset x y a base tail code pc stack (by omega) depth]
  exact zero_jump fuel _ _ code (output_pc pre offset x y a base tail pc)
    (by rw [(frame pre offset x y a base tail).1, valid]) (by omega)
    (by simp only [List.length_cons]; omega)

theorem accepted_gas (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (gas : 39 ≤ pre.gasAvailable.toNat) :
    (NativeSourceCheckedReturn.fallthrough (s10 pre offset x y a base tail) (x :: array a offset :: y :: a :: base :: tail)).gasAvailable.toNat =
      pre.gasAvailable.toNat - 39 := by
  have charged := prefix_gas pre offset x y a base tail (by omega)
  have final : (NativeSourceCheckedReturn.fallthrough (s10 pre offset x y a base tail) (x :: array a offset :: y :: a :: base :: tail)).gasAvailable.toNat =
      (s10 pre offset x y a base tail).gasAvailable.toNat - 10 :=
    NativeSourceCheckedRejection.gas_sub _ 10 (by decide) (by omega)
  omega

theorem reject_exact (fuel : Nat) (pre : EVM.State) (offset x y a base : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 239)
    (stack : pre.stack = offset :: x :: y :: a :: base :: tail)
    (invalid : flag pre a offset ≠ UInt256.ofNat 0)
    (gas : 45 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1016) :
    EVM.X (fuel + 16) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 45)) ByteArray.empty) := by
  have charged := prefix_gas pre offset x y a base tail (by omega)
  have jumpGas := NativeSourceCheckedJumpRejection.remaining_gas (s10 pre offset x y a base tail)
    (x :: array a offset :: y :: a :: base :: tail) (by omega)
  rw [NativeSourceCheckedSpan.execute_prefix (fuel + 5) _ pre offset x y a base tail code pc stack (by omega) depth]
  rw [nonzero_jump (fuel + 4) (s10 pre offset x y a base tail) (flag pre a offset) (x :: array a offset :: y :: a :: base :: tail)
    code (output_pc pre offset x y a base tail pc) (frame pre offset x y a base tail).1 invalid
    (by omega) (by simp only [List.length_cons]; omega)]
  rw [NativeSourceCheckedRejection.execute_exact fuel _
    (NativeSourceCheckedJumpRejection.afterJump (s10 pre offset x y a base tail) (x :: array a offset :: y :: a :: base :: tail)) code rfl
    (by omega) (by change (x :: array a offset :: y :: a :: base :: tail).length ≤ 1022; simp only [List.length_cons]; omega), jumpGas, charged]
  congr 3

end Compiler.Proofs.IRGeneration.NativeSourceSpanBranches
