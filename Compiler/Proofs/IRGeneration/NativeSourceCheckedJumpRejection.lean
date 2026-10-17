import Compiler.Proofs.IRGeneration.NativeSourceJumpChecks
import Compiler.Proofs.IRGeneration.NativeSourceAddressBranch

namespace Compiler.Proofs.IRGeneration.NativeSourceCheckedJumpRejection
open EvmYul EVM EVM.Proof

def afterJump (pre : EVM.State) (tail : Stack UInt256) : EVM.State :=
  { stepPre 10 pre with pc := UInt256.ofNat 91, stack := tail }

theorem transition (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0) :
    EVM.step (fuel + 1) 10 (some (.JUMPI, none)) pre = .ok (afterJump pre tail) := by
  change EvmYul.step (τ := .EVM) .JUMPI none (stepPre 10 pre) = _
  unfold EvmYul.step
  simp only [stepPre, stack]
  change Except.ok ({ stepPre 10 pre with pc := if condition != UInt256.ofNat 0 then UInt256.ofNat 91 else pre.pc + UInt256.ofNat 1, stack := tail }) = _
  have flag : (condition != UInt256.ofNat 0) = true := (NativeSourceAddressBranch.nonzero_flag condition).mpr nonzero
  simp only [flag, if_true]
  rfl

theorem continue_jump (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 962)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0)
    (gas : 10 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 2) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      EVM.X (fuel + 1) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) (afterJump pre tail) := by
  have decoded : decodeAt pre = (.JUMPI, none) := by
    unfold decodeAt; rw [code, pc, NativeSourceAddressBranch.decode962]; rfl
  have check := NativeSourceJumpChecks.rejection_jumpi pre condition tail stack
    (by simpa only [NativeSourceCheckedRejection.sub_zero_word] using gas) depth
  rw [NativeSourceCheckedRejection.zero_gas_state] at check
  exact X_succ_of_continue decoded check (transition fuel pre condition tail stack nonzero) rfl

theorem remaining_gas (pre : EVM.State) (tail : Stack UInt256) (gas : 10 ≤ pre.gasAvailable.toNat) :
    (afterJump pre tail).gasAvailable.toNat = pre.gasAvailable.toNat - 10 := by
  exact NativeSourceCheckedRejection.gas_sub _ 10 (by decide) gas

theorem execute_exact (fuel : Nat) (pre : EVM.State) (condition : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 962)
    (stack : pre.stack = UInt256.ofNat 91 :: condition :: tail) (nonzero : condition ≠ UInt256.ofNat 0)
    (gas : 16 ≤ pre.gasAvailable.toNat) (depth : tail.length ≤ 1022) :
    EVM.X (fuel + 6) (EVM.D_J NativeSourceAbiWrite.code (UInt256.ofNat 0)) pre =
      .ok (.revert (UInt256.ofNat (pre.gasAvailable.toNat - 16)) ByteArray.empty) := by
  have charged := remaining_gas pre tail (by omega)
  rw [continue_jump (fuel + 4) pre condition tail code pc stack nonzero (by omega) depth]
  rw [NativeSourceCheckedRejection.execute_exact fuel _ (afterJump pre tail) code rfl (by omega) depth]
  rw [charged]
  congr 3

end Compiler.Proofs.IRGeneration.NativeSourceCheckedJumpRejection
